/**
 * edit.js
 * Este arquivo controla toda a interatividade da página de edição e auditoria (edit.html).
 * Funções:
 * - Carregar dados essenciais (inventário, GIAP, mapeamentos).
 * - Gerenciar a tabela de inventário editável (SEÇÃO OTIMIZADA com Paginação Adaptativa).
 * - Controlar as abas e carregar seu conteúdo sob demanda (Lazy Loading).
 * - Implementar lógica de login aprimorada para evitar flicker.
 */

// Importações do módulo compartilhado
import { db, auth, idb, CACHE_DURATION_MS, loadFirebaseInventory, loadGiapInventory, loadUnitMappingFromFirestore, loadReconciledUnits, loadCustomGiapUnits } from './shared.js';
import { addAuthListener, handleLogout } from './shared.js';
import { showNotification, showOverlay, hideOverlay, normalizeStr, debounce, escapeHtml, parseCurrency } from './shared.js';
// Importações de bibliotecas do Firebase
import { doc, setDoc, updateDoc, serverTimestamp, writeBatch, addDoc, query, orderBy, limit, where, deleteDoc, collection, getDocs, getDoc, startAfter } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";

// --- ESTADO DA APLICAÇÃO ---
let fullInventory = [], giapInventory = [], customGiapUnits = [];
let giapMap = new Map();
let giapMapAllItems = new Map();
let unitMapping = {};
let dirtyItems = new Map(); // Usado pela aba otimizada
let normalizedSystemUnits = new Map();
let padroesConciliacao = [];
let linksToCreate = [];
let reconciledUnits = [];
let activeConciliationUnit = null;
let activeConciliationType = null;
let selSys = null, selGiap = null;
let giapItemsForImport = [];
let itemsToReplace = [];
let processedNfData = {};
let updatesToProcess = [];
let currentDeleteItemIds = []; // Usado pela aba otimizada

// --- ESTADO DE INICIALIZAÇÃO ---
let authReady = false; // Flag para indicar que a verificação inicial de login foi feita
let dataLoaded = false; // Flag para indicar que os dados principais foram carregados
const initializedTabs = new Set(); // Conjunto para rastrear abas já inicializadas

// --- CONFIGURAÇÕES DE PERFORMANCE (Aba Otimizada) ---
const ITEMS_PER_PAGE_DEFAULT = 50;
const MAX_ITEMS_WITHOUT_WARNING = 500;
const DEBOUNCE_DELAY = 300;
const BATCH_SIZE = 100;

// --- PAGINAÇÃO ADAPTATIVA (Aba Otimizada) ---
let currentPage = 1;
let filteredInventory = [];
let totalPages = 1;
let isFiltered = false;
let showAllItems = false;

// --- CACHE DE ELEMENTOS DOM (Aba Otimizada e Gerais) ---
const domCache = {
    // Aba Otimizada
    editTableBody: null,
    saveAllChangesBtn: null,
    pageInfo: null,
    prevPageBtn: null,
    nextPageBtn: null,
    paginationControls: null,
    filterWarning: null,
    // Gerais
    loadingScreen: null,
    authGate: null,
    feedbackStatus: null,
    navButtons: null,
    contentPanes: null,
    userEmailEdit: null
};

function initDomElements() {
    // Aba Otimizada
    domCache.editTableBody = document.getElementById('edit-table-body');
    domCache.saveAllChangesBtn = document.getElementById('save-all-changes-btn');
    domCache.pageInfo = document.getElementById('edit-page-info');
    domCache.prevPageBtn = document.getElementById('edit-prev-page');
    domCache.nextPageBtn = document.getElementById('edit-next-page');
    domCache.paginationControls = document.getElementById('pagination-controls');
    domCache.filterWarning = document.getElementById('filter-warning');
    // Gerais
    domCache.loadingScreen = document.getElementById('loading-or-error-screen');
    domCache.authGate = document.getElementById('auth-gate');
    domCache.feedbackStatus = document.getElementById('feedback-status');
    domCache.navButtons = document.querySelectorAll('#edit-nav .nav-btn');
    domCache.contentPanes = document.querySelectorAll('main > div[id^="content-"]');
    domCache.userEmailEdit = document.getElementById('user-email-edit');

    console.log("DOM elements cached.");
}

// --- FUNÇÕES UTILITÁRIAS (Normalização, Parse, etc.) ---
const normalizeTombo = (tombo) => {
    // ... (código original mantido)
    if (tombo === undefined || tombo === null || String(tombo).trim() === '') return '';
    let str = String(tombo).trim();
    if (/^0?\d+(\.0)?$/.test(str)) return String(parseInt(str, 10));
    return str;
};

function parseEstadoEOrigem(texto) {
    // ... (código original mantido)
    const textoCru = (texto || '').trim();
    if (!textoCru) return { estado: 'Regular', origem: '' };
    const validEstados = ['Novo', 'Bom', 'Regular', 'Avariado'];
    let estadoFinal = 'Regular';
    let origemFinal = '';
    for (const estado of validEstados) {
        if (normalizeStr(textoCru).startsWith(normalizeStr(estado))) {
            estadoFinal = estado;
            let resto = textoCru.substring(estado.length).trim();
            if ((resto.startsWith('(') && resto.endsWith(')')) || (resto.startsWith('[') && resto.endsWith(']'))) {
                resto = resto.substring(1, resto.length - 1).trim();
            } else if (resto.startsWith('-')) {
                resto = resto.substring(1).trim();
            }
            if (resto) {
                const restoNormalizado = normalizeStr(resto);
                if (restoNormalizado.startsWith('doação') || restoNormalizado.startsWith('doacao')) {
                    origemFinal = resto.replace(/^(doação|doacao)\s*/i, '').trim();
                }
            }
            return { estado: estadoFinal, origem: origemFinal };
        }
    }
    for (const estado of validEstados) {
        if (normalizeStr(textoCru) === normalizeStr(estado)) {
            return { estado: estado, origem: '' };
        }
    }
    return { estado: 'Regular', origem: '' };
}

// --- FUNÇÕES DE SIMILARIDADE E IA (MOVENDO carregarPadroesConciliacao PARA CIMA) ---
async function carregarPadroesConciliacao() {
    try {
        const q = query(
            collection(db, 'padroesConciliacao'),
            orderBy('timestamp', 'desc'),
            limit(300)
        );
        const snapshot = await getDocs(q);
        padroesConciliacao = snapshot.docs.map(doc => doc.data());
        console.log(`✅ ${padroesConciliacao.length} padrões de conciliação carregados`);
    } catch (error) {
        console.warn('Padrões de conciliação ainda não existem. Será criada ao salvar o primeiro vínculo.');
        padroesConciliacao = [];
    }
}

function levenshteinDistance(s1, s2) {
    const len1 = s1.length;
    const len2 = s2.length;
    if (Math.abs(len1 - len2) > 20) return Math.max(len1, len2);
    const matrix = Array(len2 + 1).fill(null).map(() => Array(len1 + 1).fill(0));
    for (let i = 0; i <= len1; i++) matrix[0][i] = i;
    for (let j = 0; j <= len2; j++) matrix[j][0] = j;
    for (let j = 1; j <= len2; j++) {
        for (let i = 1; i <= len1; i++) {
            const cost = s1[i - 1] === s2[j - 1] ? 0 : 1;
            matrix[j][i] = Math.min(
                matrix[j][i - 1] + 1,      // inserção
                matrix[j - 1][i] + 1,      // deleção
                matrix[j - 1][i - 1] + cost // substituição
            );
        }
    }
    return matrix[len2][len1];
}

function calculateSimilarity(str1, str2) {
    const s1 = normalizeStr(str1);
    const s2 = normalizeStr(str2);
    if (s1 === s2) return 1.0;
    if (s1.includes(s2) || s2.includes(s1)) return 0.92;
    const words1 = new Set(s1.split(/\s+/).filter(w => w.length > 2));
    const words2 = new Set(s2.split(/\s+/).filter(w => w.length > 2));
    if (words1.size === 0 && words2.size === 0) return 0;
    const intersection = new Set([...words1].filter(w => words2.has(w)));
    const union = new Set([...words1, ...words2]);
    const jaccardScore = union.size > 0 ? intersection.size / union.size : 0;
    let substringBonus = 0;
    const minLen = Math.min(s1.length, s2.length);
    for (let size = Math.min(8, minLen); size >= 4; size--) {
        let found = false;
        for (let i = 0; i <= s1.length - size; i++) {
            const substr = s1.substring(i, i + size);
            if (s2.includes(substr)) {
                substringBonus = Math.max(substringBonus, (size / Math.max(s1.length, s2.length)) * 0.3);
                found = true;
                break;
            }
        }
        if (found) break;
    }
    let levBonus = 0;
    if (s1.length < 50 && s2.length < 50) {
        const distance = levenshteinDistance(s1, s2);
        const maxLen = Math.max(s1.length, s2.length);
        levBonus = maxLen > 0 ? (1 - distance / maxLen) * 0.2 : 0;
    }
    return Math.min(jaccardScore * 0.6 + substringBonus + levBonus, 1.0);
}

async function salvarPadraoConciliacao(systemItem, giapItem, score) {
    const padrao = {
        descricaoSistema: systemItem.Descrição || '',
        fornecedorSistema: systemItem.Fornecedor || '',
        descricaoGIAP: `${giapItem.Descrição || ''} ${giapItem.Espécie || ''}`.trim(),
        fornecedorGIAP: giapItem['Nome Fornecedor'] || '',
        tombamento: giapItem.TOMBAMENTO,
        unidade: systemItem.Unidade || '',
        tipo: systemItem.Tipo || '',
        scoreOriginal: score,
        timestamp: serverTimestamp(),
        usuario: auth.currentUser?.email || 'unknown'
    };
    try {
        await addDoc(collection(db, 'padroesConciliacao'), padrao);
        padroesConciliacao.unshift({ ...padrao, timestamp: new Date() });
        if (padroesConciliacao.length > 300) {
            padroesConciliacao = padroesConciliacao.slice(0, 300);
        }
        console.log('✅ Padrão de conciliação salvo');
    } catch (error) {
        console.error('Erro ao salvar padrão:', error);
    }
}

function suggestGiapMatchesComAprendizado(systemItem, giapSourceItems) {
    const activeTab = document.getElementById('subtab-conciliar-sobras').classList.contains('hidden') ? 'unidade' : 'sobras';
    const giapListId = activeTab === 'sobras' ? 'sobras-giap-list' : 'giap-list';
    const context = activeTab === 'sobras' ? 'sobras' : 'default';

    if (!giapSourceItems || giapSourceItems.length === 0) {
        renderList(giapListId, [], 'TOMBAMENTO', 'Descrição', null, context);
        return;
    }

    const systemDesc = `${systemItem.Descrição || ''} ${systemItem.Fornecedor || ''}`.trim();
    const scoredItems = giapSourceItems.map(giapItem => {
        const giapDesc = `${giapItem.Descrição || ''} ${giapItem.Espécie || ''} ${giapItem['Nome Fornecedor'] || ''}`.trim();
        let baseScore = calculateSimilarity(systemDesc, giapDesc);
        if (systemItem.Fornecedor && systemItem.Fornecedor !== '-' && giapItem['Nome Fornecedor'] && giapItem['Nome Fornecedor'] !== '-') {
            const fornecedorMatch = calculateSimilarity(systemItem.Fornecedor, giapItem['Nome Fornecedor']);
            if (fornecedorMatch > 0.7) { baseScore += 0.15; }
        }
        return { item: giapItem, baseScore: Math.min(baseScore, 1.0), bonusScore: 0 };
    });

    if (padroesConciliacao.length > 0) {
        padroesConciliacao.forEach(padrao => {
            const similaridadeComPadrao = calculateSimilarity(systemDesc, `${padrao.descricaoSistema} ${padrao.fornecedorSistema}`);
            if (similaridadeComPadrao > 0.7) {
                scoredItems.forEach(scored => {
                    const giapDescCompleta = `${scored.item.Descrição || ''} ${scored.item.Espécie || ''} ${scored.item['Nome Fornecedor'] || ''}`;
                    const similaridadeComPadraoGiap = calculateSimilarity(giapDescCompleta, `${padrao.descricaoGIAP} ${padrao.fornecedorGIAP}`);
                    if (similaridadeComPadraoGiap > 0.6) {
                        const boost = similaridadeComPadrao * similaridadeComPadraoGiap * 0.2;
                        scored.bonusScore += boost;
                    }
                });
            }
        });
    }

    scoredItems.forEach(scored => { scored.finalScore = Math.min(scored.baseScore + scored.bonusScore, 1.0); });
    scoredItems.sort((a, b) => b.finalScore - a.finalScore);
    const topScore = scoredItems.length > 0 ? scoredItems[0].finalScore : 0;
    const suggestionMap = new Map(scoredItems.map(si => [si.item.TOMBAMENTO, si.finalScore]));

    renderList(giapListId, scoredItems.map(si => si.item), 'TOMBAMENTO', 'Descrição', { suggestions: suggestionMap, topScore: topScore }, context);
}

function findBestMatchForItem(pastedItem, availableSystemItems) {
    const pastedDescNorm = normalizeStr(pastedItem.descricao);
    const pastedLocalNorm = normalizeStr(pastedItem.localizacao);
    const pastedEstadoNorm = normalizeStr(pastedItem.estado);

    const findAndMark = (predicate) => {
        const index = availableSystemItems.findIndex(wrapper => !wrapper.isMatched && predicate(wrapper.item));
        if (index > -1) {
            availableSystemItems[index].isMatched = true;
            return availableSystemItems[index];
        }
        return null;
    };

    let wrapper = findAndMark(item =>
        normalizeStr(item.Descrição) === pastedDescNorm &&
        normalizeStr(item.Localização) === pastedLocalNorm &&
        normalizeStr(item.Estado) === pastedEstadoNorm
    );
    if (wrapper) return { wrapper, matchType: 'Correspondência Perfeita' };

    wrapper = findAndMark(item =>
        normalizeStr(item.Descrição) === pastedDescNorm &&
        normalizeStr(item.Localização) === pastedLocalNorm
    );
    if (wrapper) return { wrapper, matchType: 'Correspondência Alta (Descrição e Local)' };

    wrapper = findAndMark(item => normalizeStr(item.Descrição) === pastedDescNorm);
    if (wrapper) return { wrapper, matchType: 'Correspondência Exata (Descrição)' };

    const potentialMatches = availableSystemItems
        .filter(w => !w.isMatched)
        .map(w => ({ wrapper: w, score: calculateSimilarity(w.item.Descrição, pastedItem.descricao) }))
        .filter(match => match.score > 0.65)
        .sort((a, b) => b.score - a.score);

    if (potentialMatches.length > 0) {
        if (potentialMatches.length > 1 && (potentialMatches[0].score - potentialMatches[1].score) < 0.1) {
            return { wrapper: null, matchType: 'Ambigua (Similaridade)' };
        }
        const bestMatch = potentialMatches[0];
        bestMatch.wrapper.isMatched = true;
        return { wrapper: bestMatch.wrapper, matchType: `Por Similaridade (${(bestMatch.score * 100).toFixed(0)}%)` };
    }

    return { wrapper: null, matchType: 'Não Encontrado' };
}
// --- FIM DAS FUNÇÕES DE IA ---


// --- CARREGAMENTO DE DADOS PRINCIPAL ---
async function loadData(forceRefresh) {
    if (dataLoaded && !forceRefresh) {
        console.log("Data already loaded, skipping fetch.");
        return;
    }
    domCache.loadingScreen.classList.remove('hidden');
    domCache.feedbackStatus.textContent = 'Verificando cache de dados...';
    const metadata = await idb.metadata.get('lastFetch');
    const isCacheStale = !metadata || (Date.now() - metadata.timestamp > CACHE_DURATION_MS);

    if (!forceRefresh && !isCacheStale) {
        domCache.feedbackStatus.textContent = 'Carregando dados do cache local...';
        [fullInventory, giapInventory, unitMapping, customGiapUnits, reconciledUnits] = await Promise.all([
            idb.patrimonio.toArray(),
            idb.giap.toArray(),
            loadUnitMappingFromFirestore(),
            loadCustomGiapUnits(),
            loadReconciledUnits()
        ]);
        showNotification('Dados carregados do cache.', 'info');
    } else {
        domCache.feedbackStatus.textContent = 'Buscando dados atualizados do servidor...';
        try {
            [fullInventory, giapInventory, unitMapping, customGiapUnits, reconciledUnits] = await Promise.all([
                loadFirebaseInventory(),
                loadGiapInventory(),
                loadUnitMappingFromFirestore(),
                loadCustomGiapUnits(),
                loadReconciledUnits()
            ]);
            await idb.transaction('rw', idb.patrimonio, idb.giap, idb.metadata, async () => {
                await idb.patrimonio.clear(); await idb.patrimonio.bulkAdd(fullInventory);
                await idb.giap.clear(); await idb.giap.bulkAdd(giapInventory);
                await idb.metadata.put({ key: 'lastFetch', timestamp: Date.now() });
            });
            showNotification('Dados atualizados com sucesso!', 'success');
        } catch (error) {
            domCache.loadingScreen.innerHTML = `<div class="text-center"><h2 class="text-xl font-bold text-red-600">Erro ao Carregar Dados</h2><p>${error.message}</p></div>`;
            showNotification('Erro ao carregar dados do servidor.', 'error');
            dataLoaded = false;
            // Tenta carregar do cache como fallback
             try {
                 domCache.feedbackStatus.textContent = 'Falha ao buscar. Tentando carregar do cache...';
                [fullInventory, giapInventory, unitMapping, customGiapUnits, reconciledUnits] = await Promise.all([
                    idb.patrimonio.toArray(),
                    idb.giap.toArray(),
                    loadUnitMappingFromFirestore(), // Essas ainda tentam do Firestore
                    loadCustomGiapUnits(),
                    loadReconciledUnits()
                ]);
                 if (fullInventory.length > 0) {
                     showNotification('Dados carregados do cache (fallback).', 'warning');
                 } else {
                     throw new Error("Cache vazio ou inacessível."); // Força o erro se o cache também falhar
                 }
            } catch (cacheError) {
                 console.error("Erro ao carregar dados (Servidor e Cache):", error, cacheError);
                 domCache.loadingScreen.innerHTML = `<div class="text-center"><h2 class="text-xl font-bold text-red-600">Erro Crítico</h2><p>Não foi possível carregar os dados do servidor nem do cache local. Verifique sua conexão e tente recarregar a página.</p><p class="text-sm mt-2">${error.message}</p></div>`;
                 return; // Impede a continuação
            }
        }
    }

    // Processamento essencial dos dados
    giapMap = new Map(giapInventory
        .filter(item => normalizeStr(item.Status).includes(normalizeStr('Disponível')))
        .map(item => [normalizeTombo(item['TOMBAMENTO']), item])
    );
    giapMapAllItems = new Map(giapInventory.map(item => [normalizeTombo(item['TOMBAMENTO']), item]));

    normalizedSystemUnits.clear();
    fullInventory.forEach(item => {
        if (item.Unidade) {
            const normalized = normalizeStr(item.Unidade);
            if (!normalizedSystemUnits.has(normalized)) {
                normalizedSystemUnits.set(normalized, item.Unidade.trim());
            }
        }
    });

    // Chama a função que foi movida para cima
    await carregarPadroesConciliacao();

    dataLoaded = true;
    domCache.feedbackStatus.textContent = `Pronto. ${fullInventory.length} itens carregados.`;
    domCache.loadingScreen.classList.add('hidden');
    console.log("Data loading complete.");

    // Inicializa a primeira aba visível (geralmente 'edicao')
    const initialTab = document.querySelector('#edit-nav .nav-btn.active')?.dataset.tab || 'edicao';
    initializeTabContent(initialTab);

}


// --- LÓGICA DE INICIALIZAÇÃO E RENDERIZAÇÃO DAS ABAS (Lazy Loading) ---

function initializeTabContent(tabName) {
    if (!dataLoaded) {
        console.warn("Attempted to initialize tab before data was loaded.");
        return;
    }
    if (initializedTabs.has(tabName)) {
        console.log(`Tab ${tabName} already initialized.`);
        // Re-executa a função de renderização principal da aba para garantir atualização
        // Exceto para a aba 'edicao' que tem sua própria lógica de re-render
        if (tabName !== 'edicao') {
             try {
                switch (tabName) {
                    case 'unidades': populateUnitMappingTab(); break;
                    case 'conciliar': /* A lógica de sub-abas cuida disso */ break;
                    case 'sobrando': initSobrantesTab(); break; // Re-executa busca
                    case 'transferencias': populatePendingTransfersTab(); break;
                    case 'importacao': /* A lógica de sub-abas cuida disso */ break;
                    case 'notas_fiscais': renderNfList(); break;
                    case 'giap': populateGiapTab(); break;
                }
            } catch (error) {
                 console.error(`Error re-rendering tab ${tabName}:`, error);
            }
        }
        return;
    }

    console.log(`Initializing tab: ${tabName}`);
    try {
        switch (tabName) {
            case 'edicao':
                initEditableInventoryTab();
                break;
            case 'unidades':
                initUnitMappingTab();
                break;
            case 'conciliar':
                initReconciliationTab();
                break;
             case 'sobrando':
                 initSobrantesTab();
                 break;
            case 'transferencias':
                initPendingTransfersTab();
                break;
            case 'importacao':
                initImportAndReplaceTab();
                break;
            case 'notas_fiscais':
                initNfTab();
                break;
            case 'giap':
                initGiapTab();
                break;
            default:
                console.warn(`No initialization logic for tab: ${tabName}`);
        }
        initializedTabs.add(tabName);
    } catch (error) {
        console.error(`Error initializing tab ${tabName}:`, error);
        showNotification(`Erro ao carregar a aba ${tabName}.`, 'error');
    }
}

// --- FUNÇÕES DE INICIALIZAÇÃO POR ABA ---

function initEditableInventoryTab() {
    console.log("Initializing Editable Inventory Tab");
    // Popula os filtros da aba editável
    const tipos = [...new Set(fullInventory.map(i => i.Tipo))].filter(Boolean).sort();
    const unidades = [...new Set(fullInventory.map(i => i.Unidade))].filter(Boolean).sort();
    const tipoSelect = document.getElementById('edit-filter-tipo');
    const unidadeSelect = document.getElementById('edit-filter-unidade');
    tipoSelect.innerHTML = '<option value="">Todos os Tipos</option>' + tipos.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');
    unidadeSelect.innerHTML = '<option value="">Todas as Unidades</option>' + unidades.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`).join('');

    // Aplica filtros/paginação iniciais e configura eventos
    applyFiltersAndPaginate();
    setupEventDelegation(); // Configura os listeners otimizados
}

function initUnitMappingTab() {
    console.log("Initializing Unit Mapping Tab");
    populateUnitMappingTab(); // Chama a função original que popula a UI
    // Adiciona listeners específicos desta aba aqui, se necessário
    document.getElementById('map-filter-tipo')?.addEventListener('change', updateSystemUnitOptions);
    document.getElementById('map-system-unit-select')?.addEventListener('change', updateGiapUnitOptions);
    document.getElementById('map-giap-filter')?.addEventListener('input', debounce(updateGiapUnitOptions, 300));
    document.getElementById('save-mapping-btn')?.addEventListener('click', handleSaveMapping); // Criar handleSaveMapping
    document.getElementById('saved-mappings-container')?.addEventListener('click', handleDeleteMapping); // Criar handleDeleteMapping
}

function initReconciliationTab() {
    console.log("Initializing Reconciliation Tab");
    populateReconciliationTab(); // Chama a função original
    // Adiciona listeners específicos
    document.getElementById('filter-tipo')?.addEventListener('change', handleConciliationTypeChange); // Criar handle...
    document.getElementById('load-conciliar')?.addEventListener('click', handleLoadConciliation); // Criar handle...
    const debouncedRenderConciliation = debounce(renderConciliationLists, 300);
    document.getElementById('system-list-filter')?.addEventListener('input', debouncedRenderConciliation);
    document.getElementById('giap-list-filter')?.addEventListener('input', debouncedRenderConciliation);
    document.getElementById('clear-selections')?.addEventListener('click', handleClearConciliationSelections); // Criar handle...
    document.getElementById('save-links')?.addEventListener('click', () => savePendingLinks('unidade').then(handleSaveLinksResult)); // Criar handle...
    document.getElementById('finish-reconciliation-btn')?.addEventListener('click', handleFinishReconciliation); // Criar handle...
    document.getElementById('created-links')?.addEventListener('click', handleDeleteCreatedLink); // Criar handle...
    document.getElementById('import-giap-btn')?.addEventListener('click', handleImportGiapItems); // Criar handle...

    // Listeners das sub-abas de conciliação
    const subNavButtonsConciliar = document.querySelectorAll('#content-conciliar .sub-nav-btn');
    subNavButtonsConciliar.forEach(button => {
        button.addEventListener('click', handleConciliationSubTabSwitch); // Criar handle...
    });

    // Adiciona listeners para a sub-aba Sobras (se necessário)
    document.getElementById('load-sobras-conciliar')?.addEventListener('click', renderSobrantesConciliation);
    const debouncedRenderSobrantes = debounce(renderSobrantesConciliation, 300);
    document.getElementById('sobras-system-list-filter')?.addEventListener('input', debouncedRenderSobrantes);
    document.getElementById('sobras-giap-list-filter')?.addEventListener('input', debouncedRenderSobrantes);
    document.getElementById('sobras-giap-type-filter')?.addEventListener('change', debouncedRenderSobrantes);
    document.getElementById('sobras-save-links')?.addEventListener('click', () => savePendingLinks('sobras').then(handleSaveLinksResultSobras)); // Criar handle...
    document.getElementById('sobras-clear-selections')?.addEventListener('click', handleClearSobrantesSelections); // Criar handle...
    document.getElementById('sobras-created-links')?.addEventListener('click', handleDeleteCreatedLinkSobras); // Criar handle...

     // Listeners sub-aba Itens a Tombar
    document.getElementById('tombar-filter-tipo')?.addEventListener('change', handleTombarFilterChange); // Criar handle...
    document.getElementById('tombar-filter-unidade')?.addEventListener('change', renderItensATombar);
    document.getElementById('itens-a-tombar-container')?.addEventListener('click', handleConfirmTombamento); // Criar handle...
}

function initSobrantesTab() {
    console.log("Initializing Sobrantes Tab");
    document.getElementById('suggest-sobrando')?.addEventListener('click', () => {
        const keyword = normalizeStr(document.getElementById('leftover-keyword').value);
        const tomboFilter = normalizeStr(document.getElementById('leftover-tombo').value);
        const leftovers = getGlobalLeftovers();

        const filtered = leftovers.filter(item => {
            const tomboItem = normalizeTombo(item.TOMBAMENTO);
            const descItem = normalizeStr(item.Descrição || item.Espécie);
            const matchesKeyword = !keyword || descItem.includes(keyword);
            const matchesTombo = !tomboFilter || tomboItem.includes(tomboFilter);
            return matchesKeyword && matchesTombo;
        });
        const totalEl = document.getElementById('total-sobrando');
        if (totalEl) totalEl.textContent = filtered.length;
        renderList('sobrando-list', filtered, 'TOMBAMENTO', 'Descrição', null, 'sobras');
    });
    // Força a primeira busca se houver dados
    if(dataLoaded) document.getElementById('suggest-sobrando')?.click();
}

function initPendingTransfersTab() {
    console.log("Initializing Pending Transfers Tab");
    populatePendingTransfersTab(); // Chama a função original
    // Adiciona listeners específicos
    document.getElementById('pending-transfers-container')?.addEventListener('click', handleTransferAction); // Criar handle...
}

function initImportAndReplaceTab() {
    console.log("Initializing Import/Replace Tab");
    populateImportAndReplaceTab(); // Chama a função original
    // Adiciona listeners específicos
     const subNavButtonsImport = document.querySelectorAll('#content-importacao .sub-nav-btn');
     subNavButtonsImport.forEach(button => {
         button.addEventListener('click', handleImportSubTabSwitch); // Criar handle...
     });
     // Sub-aba Substituir
     document.getElementById('preview-replace-btn')?.addEventListener('click', handlePreviewReplace); // Criar handle...
     document.getElementById('replace-confirm-checkbox')?.addEventListener('change', handleReplaceConfirmChange); // Criar handle...
     document.getElementById('confirm-replace-btn')?.addEventListener('click', handleConfirmReplace); // Criar handle...
     // Sub-aba Editar por Descrição
     document.getElementById('preview-edit-by-desc-btn')?.addEventListener('click', handlePreviewEditByDesc); // Criar handle...
     document.getElementById('edit-by-desc-preview-table-container')?.addEventListener('change', handleEditByDescCheckboxChange); // Criar handle...
     document.getElementById('confirm-edit-by-desc-btn')?.addEventListener('click', handleConfirmEditByDesc); // Criar handle...
     // Sub-aba Importar por Tombamento
     document.getElementById('mass-transfer-search-btn')?.addEventListener('click', handleMassTransferSearch); // Criar handle...
     document.getElementById('mass-transfer-set-all-status')?.addEventListener('change', handleMassTransferSetAllStatus); // Criar handle...
     document.getElementById('mass-transfer-confirm-btn')?.addEventListener('click', handleMassTransferConfirm); // Criar handle...
     // Sub-aba Adicionar Unidade GIAP
     document.getElementById('save-giap-unit-btn')?.addEventListener('click', handleSaveGiapUnit); // Criar handle...
}

function initNfTab() {
    console.log("Initializing NF Tab");
    populateNfTab(); // Chama a função original
    // Adiciona listeners específicos
    const debouncedRenderNf = debounce(renderNfList, 300);
    document.getElementById('nf-search')?.addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-item-search')?.addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-fornecedor-search')?.addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-tipo-entrada')?.addEventListener('change', renderNfList);
    document.getElementById('nf-status-filter')?.addEventListener('change', renderNfList);
    document.getElementById('nf-date-start')?.addEventListener('change', renderNfList);
    document.getElementById('nf-date-end')?.addEventListener('change', renderNfList);
    document.getElementById('clear-nf-filters-btn')?.addEventListener('click', handleClearNfFilters); // Criar handle...
}

function initGiapTab() {
    console.log("Initializing GIAP Tab");
    populateGiapTab(); // Chama a função original
}

// --- FIM: FUNÇÕES DE INICIALIZAÇÃO POR ABA ---


// --- INÍCIO: SEÇÃO ULTRA OTIMIZADA (Funções coladas) ---

// --- LÓGICA ADAPTATIVA DE FILTROS ---
function applyFiltersAndPaginate() {
    // Adiciona verificação se os elementos existem
    const tipoEl = document.getElementById('edit-filter-tipo');
    const unidadeEl = document.getElementById('edit-filter-unidade');
    const estadoEl = document.getElementById('edit-filter-estado');
    const descricaoEl = document.getElementById('edit-filter-descricao');

    const tipo = tipoEl ? tipoEl.value : '';
    const unidade = unidadeEl ? unidadeEl.value : '';
    const estado = estadoEl ? estadoEl.value : '';
    const descricao = descricaoEl ? normalizeStr(descricaoEl.value) : '';


    // Detectar se há QUALQUER filtro ativo
    isFiltered = !!(tipo || unidade || estado || descricao);

    // Filtrar inventário
    filteredInventory = fullInventory.filter(item => {
        if (tipo && item.Tipo !== tipo) return false;
        if (unidade && item.Unidade !== unidade) return false;
        if (estado && item.Estado !== estado) return false;
        if (descricao && !normalizeStr(item.Descrição || '').includes(descricao)) return false;
        return true;
    });

    // LÓGICA ADAPTATIVA:
    // Se filtrado = mostrar TODOS os resultados (para edição em massa)
    // Se não filtrado = usar paginação (performance)
    if (isFiltered) {
        showAllItems = true;
        totalPages = 1;
        currentPage = 1;

        // Aviso se muitos itens
        if (filteredInventory.length > MAX_ITEMS_WITHOUT_WARNING && domCache.filterWarning) {
            domCache.filterWarning.classList.remove('hidden');
            domCache.filterWarning.innerHTML = `
                <strong>⚠️ Atenção:</strong> ${filteredInventory.length} itens encontrados.
                Considere refinar os filtros para melhorar a performance.
            `;
        } else if (domCache.filterWarning) {
            domCache.filterWarning.classList.add('hidden');
        }

        // Esconder controles de paginação
        if(domCache.paginationControls) domCache.paginationControls.classList.add('hidden');
    } else {
        showAllItems = false;
        totalPages = Math.max(1, Math.ceil(filteredInventory.length / ITEMS_PER_PAGE_DEFAULT));
        currentPage = Math.min(currentPage, totalPages);
        if(domCache.filterWarning) domCache.filterWarning.classList.add('hidden');
        if(domCache.paginationControls) domCache.paginationControls.classList.remove('hidden');
    }

    renderEditableTable();
    updatePaginationControls();
}

// --- RENDERIZAÇÃO OTIMIZADA ---
function renderEditableTable() {
    if (!domCache.editTableBody) {
        console.error("editTableBody not found in cache during render");
        return;
    }

    const startTime = performance.now();

    // Determinar quais itens renderizar
    let itemsToRender;
    if (showAllItems) {
        // Mostrar TODOS os filtrados
        itemsToRender = filteredInventory;
    } else {
        // Paginação normal
        const start = (currentPage - 1) * ITEMS_PER_PAGE_DEFAULT;
        const end = start + ITEMS_PER_PAGE_DEFAULT;
        itemsToRender = filteredInventory.slice(start, end);
    }

    // Usar DocumentFragment para renderização super rápida
    const fragment = document.createDocumentFragment();

    // Renderizar em lote
    itemsToRender.forEach(item => {
        const itemData = dirtyItems.get(item.id) || item; // Pega dados 'sujos' se existirem
        const tr = document.createElement('tr');
        tr.dataset.id = item.id;
        tr.className = dirtyItems.has(item.id) ? 'edited-row' : '';

        const giapItem = giapMap.get(normalizeTombo(itemData.Tombamento));
        const hasGiap = !!giapItem;
        const tomboReadonly = hasGiap ? 'readonly title="Vinculado ao GIAP"' : '';

        tr.innerHTML = `
            <td class="px-2 py-1 text-xs whitespace-nowrap">${escapeHtml(itemData.Tipo || '')}</td>
            <td class="px-2 py-1 text-xs whitespace-nowrap">${escapeHtml(itemData.Unidade || '')}</td>
            <td class="px-2 py-1 text-xs">
                <input type="text" class="w-full p-1 border rounded text-xs editable-field"
                       data-field="Tombamento" data-id="${item.id}"
                       value="${escapeHtml(itemData.Tombamento || '')}" ${tomboReadonly}>
            </td>
            <td class="px-2 py-1 text-xs" style="min-width: 200px;">
                <input type="text" class="w-full p-1 border rounded text-xs editable-field"
                       data-field="Descrição" data-id="${item.id}"
                       value="${escapeHtml(itemData.Descrição || '')}">
            </td>
            <td class="px-2 py-1 text-xs" style="min-width: 150px;">
                <input type="text" class="w-full p-1 border rounded text-xs editable-field"
                       data-field="Fornecedor" data-id="${item.id}"
                       value="${escapeHtml(itemData.Fornecedor || '')}">
            </td>
            <td class="px-2 py-1 text-xs" style="min-width: 150px;">
                <input type="text" class="w-full p-1 border rounded text-xs editable-field"
                       data-field="Localização" data-id="${item.id}"
                       value="${escapeHtml(itemData.Localização || '')}">
            </td>
            <td class="px-2 py-1 text-xs">
                <select class="w-full p-1 border rounded text-xs editable-field"
                        data-field="Estado" data-id="${item.id}">
                    <option value="Novo" ${itemData.Estado === 'Novo' ? 'selected' : ''}>Novo</option>
                    <option value="Bom" ${itemData.Estado === 'Bom' ? 'selected' : ''}>Bom</option>
                    <option value="Regular" ${itemData.Estado === 'Regular' ? 'selected' : ''}>Regular</option>
                    <option value="Avariado" ${itemData.Estado === 'Avariado' ? 'selected' : ''}>Avariado</option>
                </select>
            </td>
            <td class="px-2 py-1 text-xs" style="min-width: 150px;">
                <textarea class="w-full p-1 border rounded text-xs editable-field" rows="1"
                          data-field="Observação" data-id="${item.id}">${escapeHtml(itemData.Observação || '')}</textarea>
            </td>
            <td class="px-2 py-1 text-center">
                <button class="text-red-600 hover:text-red-800 delete-item-btn text-lg"
                        data-id="${item.id}" title="Excluir item">
                    <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" class="pointer-events-none" viewBox="0 0 16 16"><path d="M5.5 5.5A.5.5 0 0 1 6 6v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m2.5 0a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m3 .5a.5.5 0 0 0-1 0v6a.5.5 0 0 0 1 0V6z"/><path fill-rule="evenodd" d="M14.5 3a1 1 0 0 1-1 1H13v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V4h-.5a1 1 0 0 1-1-1V2a1 1 0 0 1 1-1H6a1 1 0 0 1 1-1h2a1 1 0 0 1 1 1h3.5a1 1 0 0 1 1 1v1zM4.118 4 4 4.059V13a1 1 0 0 0 1 1h6a1 1 0 0 0 1-1V4.059L11.882 4H4.118zM2.5 3h11V2h-11v1z"/></svg>
                </button>
            </td>
        `;

        fragment.appendChild(tr);
    });

    // Limpar e inserir de uma vez (super rápido)
    // Usar requestAnimationFrame pode suavizar a renderização visual, especialmente com muitos itens
    requestAnimationFrame(() => {
        domCache.editTableBody.innerHTML = '';
        domCache.editTableBody.appendChild(fragment);
    });


    const renderTime = (performance.now() - startTime).toFixed(0);
    console.log(`✅ ${itemsToRender.length} itens renderizados em ${renderTime}ms (Render Function)`);
}

function updatePaginationControls() {
    if (!domCache.pageInfo) return;

    if (showAllItems) {
        // Modo filtrado - mostrar todos
        domCache.pageInfo.innerHTML = `
            <span class="text-green-600 font-semibold">
                📋 Mostrando TODOS os ${filteredInventory.length} itens filtrados
            </span>
            ${dirtyItems.size > 0 ? `<span class="text-orange-600 ml-3">✏️ ${dirtyItems.size} alterações pendentes</span>` : ''}
        `;
    } else {
        // Modo paginado
        const start = filteredInventory.length === 0 ? 0 : (currentPage - 1) * ITEMS_PER_PAGE_DEFAULT + 1;
        const end = Math.min(currentPage * ITEMS_PER_PAGE_DEFAULT, filteredInventory.length);

        domCache.pageInfo.innerHTML = `
            Mostrando ${start}-${end} de ${filteredInventory.length} itens (Página ${currentPage}/${totalPages})
            ${dirtyItems.size > 0 ? `<span class="text-orange-600 ml-3">✏️ ${dirtyItems.size} alterações</span>` : ''}
        `;

        if(domCache.prevPageBtn) domCache.prevPageBtn.disabled = currentPage === 1;
        if(domCache.nextPageBtn) domCache.nextPageBtn.disabled = currentPage === totalPages;
    }

    // Botão salvar
    if(domCache.saveAllChangesBtn) {
        domCache.saveAllChangesBtn.disabled = dirtyItems.size === 0;
        if (dirtyItems.size > 0) {
            domCache.saveAllChangesBtn.textContent = `💾 Salvar ${dirtyItems.size} Alterações`;
            domCache.saveAllChangesBtn.classList.add('animate-pulse');
        } else {
            domCache.saveAllChangesBtn.textContent = '💾 Salvar Alterações';
            domCache.saveAllChangesBtn.classList.remove('animate-pulse');
        }
    }
}

// --- EVENT DELEGATION (Ultra eficiente) ---
function setupEventDelegation() {
    if (!domCache.editTableBody) return;
    // Remove listeners antigos para evitar duplicação se chamado mais de uma vez
    domCache.editTableBody.removeEventListener('input', handleTableInput);
    domCache.editTableBody.removeEventListener('click', handleTableClick);

    // Adiciona os listeners
    domCache.editTableBody.addEventListener('input', handleTableInput);
    domCache.editTableBody.addEventListener('click', handleTableClick);
    console.log("Event delegation setup complete.");
}

// Handler separado para input
function handleTableInput(e) {
    const field = e.target;
    if (!field.classList.contains('editable-field')) return;

    const itemId = field.dataset.id;
    const fieldName = field.dataset.field;
    let newValue = field.value; // NÂO usar .trim() aqui

    const item = fullInventory.find(i => i.id === itemId);
    if (!item) return;

    const currentItemState = dirtyItems.get(itemId) || item;

    // Verifica se houve mudança real (comparando com o estado atual, seja original ou já modificado)
    if (currentItemState[fieldName] !== newValue) {
        const updatedItem = { ...currentItemState, [fieldName]: newValue };
        dirtyItems.set(itemId, updatedItem);
        field.closest('tr').classList.add('edited-row');
        updatePaginationControls();
    } else {
         // Se voltou ao valor original (comparado ao item base), remove do dirtyItems
         // ATENÇÃO: Esta lógica pode ser complexa se houver múltiplas edições.
         // Uma abordagem mais simples é apenas marcar como sujo na primeira mudança.
         // Para simplificar, vamos manter a lógica atual: qualquer input marca como 'dirty'.
         // A verificação se o valor final é igual ao original pode ser feita no save, se necessário.
         const updatedItem = { ...currentItemState, [fieldName]: newValue };
         dirtyItems.set(itemId, updatedItem); // Garante que está no map
         field.closest('tr').classList.add('edited-row');
         updatePaginationControls();
    }
}

// Handler separado para click
function handleTableClick(e) {
    const deleteBtn = e.target.closest('.delete-item-btn');
    if (!deleteBtn) return;

    const itemId = deleteBtn.dataset.id;
    openDeleteConfirmModal([itemId]);
}


// --- SALVAR ALTERAÇÕES EM LOTE ---
async function saveAllChanges() {
    if (dirtyItems.size === 0) {
        showNotification('Nenhuma alteração para salvar.', 'info');
        return;
    }

    const itemsCount = dirtyItems.size;
    showOverlay(`Salvando ${itemsCount} alterações...`);

    try {
        const itemsToSave = Array.from(dirtyItems.values());
        let savedCount = 0;

        // Processar em lotes de BATCH_SIZE
        for (let i = 0; i < itemsToSave.length; i += BATCH_SIZE) {
            const chunk = itemsToSave.slice(i, i + BATCH_SIZE);
            const chunkBatch = writeBatch(db);

            chunk.forEach(itemWithChanges => {
                const docRef = doc(db, 'patrimonio', itemWithChanges.id);
                // Limpa o ID antes de salvar para não dar erro no firestore
                const { id, createdAt, ...dataToSave } = itemWithChanges; // Remove id e createdAt (imutável)
                // Garante que todos os campos sejam strings ou tipos válidos antes de salvar
                const sanitizedData = Object.entries(dataToSave).reduce((acc, [key, value]) => {
                    // Trata especificamente campos que podem ser números ou datas se necessário
                    // Por padrão, converte null/undefined para string vazia
                    acc[key] = (value === null || value === undefined) ? '' : value;
                    return acc;
                }, {});

                chunkBatch.update(docRef, {
                    ...sanitizedData,
                    updatedAt: serverTimestamp() // Atualiza timestamp
                });
            });

            await chunkBatch.commit();
            savedCount += chunk.length;
            showOverlay(`Salvando: ${savedCount}/${itemsToSave.length} itens...`);
        }

        // Atualizar cache local e array principal
        await idb.transaction('rw', idb.patrimonio, async () => {
            const itemsToCache = [];
            itemsToSave.forEach(itemWithChanges => {
                const index = fullInventory.findIndex(i => i.id === itemWithChanges.id);
                if (index > -1) {
                    // Mescla as mudanças no item original do inventário
                    fullInventory[index] = { ...fullInventory[index], ...itemWithChanges };
                    itemsToCache.push(fullInventory[index]); // Adiciona item atualizado para cache
                }
            });
            if (itemsToCache.length > 0) {
                await idb.patrimonio.bulkPut(itemsToCache);
            }
        });

        dirtyItems.clear(); // Limpa apenas após sucesso
        hideOverlay();
        showNotification(`✅ ${itemsCount} itens salvos com sucesso!`, 'success');

        // Re-renderizar para remover marcações de edição
        renderEditableTable();
        updatePaginationControls();
    } catch (error) {
        hideOverlay();
        showNotification(`❌ Erro ao salvar: ${error.message}`, 'error');
        console.error('Erro detalhado ao salvar:', error);
    }
}


// --- PAGINAÇÃO ---
function goToPage(page) {
    currentPage = Math.max(1, Math.min(page, totalPages));
    renderEditableTable();
    updatePaginationControls();
    // Scroll to top of table container
    const tableContainer = domCache.editTableBody?.closest('.overflow-auto');
    if (tableContainer) tableContainer.scrollTop = 0;
}

// --- MODAL DE EXCLUSÃO ---
function openDeleteConfirmModal(itemIds) {
    currentDeleteItemIds = itemIds;
    const modal = document.getElementById('delete-confirm-modal-edit');
    const listEl = document.getElementById('delete-items-list');
    if (!modal || !listEl) return; // Verifica se elementos existem

    const itemsDesc = itemIds.map(id => {
        const item = fullInventory.find(i => i.id === id);
        // Usa ?? para fallback caso Tombamento ou Descrição sejam null/undefined
        return item ? `${item.Tombamento ?? 'S/T'} - ${item.Descrição ?? 'Descrição Indisponível'}` : 'Item desconhecido';
    }).slice(0, 5).join('<br>'); // Mostra até 5 itens

    listEl.innerHTML = itemsDesc + (itemIds.length > 5 ? `<br>... e mais ${itemIds.length - 5} itens.` : '');
    modal.classList.remove('hidden');
}

function closeDeleteConfirmModal() {
    const modal = document.getElementById('delete-confirm-modal-edit');
    if(modal) modal.classList.add('hidden');
    currentDeleteItemIds = [];
}

async function confirmDeleteItems() {
    if (currentDeleteItemIds.length === 0) return;

    const count = currentDeleteItemIds.length;
    showOverlay(`Excluindo ${count} itens...`);

    try {
        const batch = writeBatch(db);
        currentDeleteItemIds.forEach(id => {
            batch.delete(doc(db, 'patrimonio', id));
        });
        await batch.commit();

        // Atualizar localmente
        const idsToDeleteSet = new Set(currentDeleteItemIds);
        fullInventory = fullInventory.filter(item => !idsToDeleteSet.has(item.id));
        // Recalcula filteredInventory baseado no fullInventory atualizado
        applyFiltersAndPaginate(); // Isso já re-renderiza a tabela

        await idb.patrimonio.bulkDelete(currentDeleteItemIds);

        // Limpar alterações pendentes dos itens deletados
        currentDeleteItemIds.forEach(id => dirtyItems.delete(id));

        hideOverlay();
        closeDeleteConfirmModal();
        showNotification(`✅ ${count} itens excluídos!`, 'success');
        // applyFiltersAndPaginate(); // Chamada redundante, já feita acima
    } catch (error) {
        hideOverlay();
        showNotification(`❌ Erro ao excluir: ${error.message}`, 'error');
        console.error(error);
    }
}

// --- FIM: SEÇÃO ULTRA OTIMIZADA (Funções coladas) ---


// --- SEÇÃO ORIGINAL MANTIDA (Outras Abas) ---
// (Cole as funções originais aqui, ajustando nomes se necessário para evitar conflitos)
// ... (populateUnitMappingTab, updateSystemUnitOptions, etc., como na versão anterior) ...
function populateUnitMappingTab() {
    // ... (código original mantido)
    const systemTypes = [...new Set(fullInventory.map(i => i.Tipo).filter(Boolean))].sort();
    const mapFilterTipo = document.getElementById('map-filter-tipo');
    mapFilterTipo.innerHTML = '<option value="">Todos os Tipos</option>' + systemTypes.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');
    updateSystemUnitOptions();
    renderSavedMappings();
    updateGiapUnitOptions();
}

function updateSystemUnitOptions() {
    // ... (código original mantido)
    const mapSystemUnitSelect = document.getElementById('map-system-unit-select');
    if (!mapSystemUnitSelect) return; // Verifica
    const selectedType = document.getElementById('map-filter-tipo').value;
    const linkedSystemUnits = Object.keys(unitMapping);
    const systemUnits = [...normalizedSystemUnits.values()].filter(unit => {
        const item = fullInventory.find(i => i.Unidade === unit);
        const isCorrectType = !selectedType || item?.Tipo === selectedType;
        return isCorrectType && !linkedSystemUnits.includes(unit);
    }).sort();
    mapSystemUnitSelect.innerHTML = systemUnits.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`).join('');
}

function updateGiapUnitOptions() {
    // ... (código original mantido)
    const mapGiapUnitMultiselect = document.getElementById('map-giap-unit-multiselect');
    const mapGiapFilter = document.getElementById('map-giap-filter');
    if (!mapGiapUnitMultiselect || !mapGiapFilter) return; // Verifica

    const filterText = normalizeStr(mapGiapFilter.value);
    let allGiapUnitsFromSheet = [...new Set(giapInventory.map(i => i.Unidade).filter(Boolean))];
    let allGiapUnits = [...new Set([...allGiapUnitsFromSheet, ...customGiapUnits.map(u => u.name)])].sort();

    const mapSystemUnitSelect = document.getElementById('map-system-unit-select');
    const selectedSystemUnits = mapSystemUnitSelect ? Array.from(mapSystemUnitSelect.selectedOptions).map(opt => opt.value) : [];


    const allLinkedGiapUnits = new Set(Object.values(unitMapping).flat());
    const currentMapping = new Set();
    selectedSystemUnits.forEach(unit => {
        if (unitMapping[unit]) {
            unitMapping[unit].forEach(giapUnit => currentMapping.add(giapUnit));
        }
    });

    if (filterText) {
        allGiapUnits = allGiapUnits.filter(unit => normalizeStr(unit).includes(filterText));
    }

    const keywords = new Set();
    selectedSystemUnits.forEach(unit => {
        unit.split('/').forEach(part => {
             const trimmedPart = part.trim();
             if (trimmedPart) keywords.add(normalizeStr(trimmedPart)); // Evita adicionar keywords vazias
        });
    });


    const suggestions = [];
    const available = [];
    const usedByOthers = [];

    allGiapUnits.forEach(unit => {
        const optionHtml = `<option value="${escapeHtml(unit)}">${escapeHtml(unit)}</option>`;
        const isSuggestion = keywords.size > 0 && Array.from(keywords).some(kw => kw && normalizeStr(unit).includes(kw));

        if (!allLinkedGiapUnits.has(unit) || currentMapping.has(unit)) {
            if (isSuggestion && !filterText) {
                suggestions.push(optionHtml);
            } else {
                available.push(optionHtml);
            }
        } else {
            usedByOthers.push(optionHtml);
        }
    });

    const suggestionHeader = suggestions.length > 0 ? `<optgroup label="Sugestões">` : '';
    const suggestionFooter = suggestions.length > 0 ? `</optgroup>` : '';
    const usedHeader = usedByOthers.length > 0 ? `<optgroup label="Já Mapeadas (em outras unidades)">` : '';
    const usedFooter = usedByOthers.length > 0 ? `</optgroup>` : '';

    mapGiapUnitMultiselect.innerHTML = suggestionHeader + suggestions.join('') + suggestionFooter + available.join('') + usedHeader + usedByOthers.join('') + usedFooter;
}


function renderSavedMappings() {
    // ... (código original mantido)
    const savedMappingsContainer = document.getElementById('saved-mappings-container');
    if (!savedMappingsContainer) return; // Verifica
    const mappedUnits = Object.keys(unitMapping).filter(key => unitMapping[key]?.length > 0).sort();
    savedMappingsContainer.innerHTML = mappedUnits.length > 0 ? mappedUnits.map(systemUnit => `
        <div class="p-2 border rounded-md bg-slate-50 flex justify-between items-center">
            <div><strong class="text-sm">${escapeHtml(systemUnit)}</strong><p class="text-xs text-slate-600">→ ${unitMapping[systemUnit].join(', ')}</p></div>
            <button class="delete-mapping-btn text-red-500 hover:text-red-700 p-1" data-system-unit="${escapeHtml(systemUnit)}">
                <svg class="pointer-events-none" xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" viewBox="0 0 16 16"><path d="M5.5 5.5A.5.5 0 0 1 6 6v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m2.5 0a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m3 .5a.5.5 0 0 0-1 0v6a.5.5 0 0 0 1 0V6z"/><path fill-rule="evenodd" d="M14.5 3a1 1 0 0 1-1 1H13v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V4h-.5a1 1 0 0 1-1-1V2a1 1 0 0 1 1-1H6a1 1 0 0 1 1-1h2a1 1 0 0 1 1 1h3.5a1 1 0 0 1 1 1v1zM4.118 4 4 4.059V13a1 1 0 0 0 1 1h6a1 1 0 0 0 1-1V4.059L11.882 4H4.118zM2.5 3h11V2h-11v1z"/></svg>
            </button>
        </div>`).join('') : `<p class="text-sm text-slate-500">Nenhuma ligação salva ainda.</p>`;
}

function populatePendingTransfersTab() {
    // ... (código original mantido)
    const pendingTransfersContainer = document.getElementById('pending-transfers-container');
     if (!pendingTransfersContainer) return; // Verifica
     const pendingTransfers = fullInventory.filter(item => {
        const tombo = item.Tombamento?.trim();
        if (!tombo || normalizeStr(tombo).includes('permuta') || tombo.toLowerCase() === 's/t') return false;

        const giapItem = giapMap.get(tombo); // Usa giapMap que já está filtrado por 'Disponível'
        if (!giapItem) return false; // Se não está disponível, não é transferência pendente

        const systemUnit = (item.Unidade || '').trim();
        const giapUnit = giapItem.Unidade;
        if (!systemUnit || !giapUnit) return false;

        if (!unitMapping[systemUnit] || unitMapping[systemUnit].length === 0) {
            // Se não há mapeamento, compara diretamente (normalizado)
            return normalizeStr(systemUnit) !== normalizeStr(giapUnit);
        }

        // Se há mapeamento, verifica se a unidade GIAP está entre as mapeadas
        const mappedGiapUnits = unitMapping[systemUnit];
        return !mappedGiapUnits.map(u => normalizeStr(u)).includes(normalizeStr(giapUnit));
    });


    const groupedTransfers = pendingTransfers.reduce((acc, item) => {
        const tipo = item.Tipo || 'Sem Tipo';
        if (!acc[tipo]) acc[tipo] = {};

        const unit = item.Unidade || 'Unidade Desconhecida';
        if (!acc[tipo][unit]) {
            acc[tipo][unit] = [];
        }
        acc[tipo][unit].push(item);
        return acc;
    }, {});

    const tipos = Object.keys(groupedTransfers).sort();

    if (tipos.length === 0) {
        pendingTransfersContainer.innerHTML = `<p class="text-slate-500 text-center p-4">Nenhuma transferência pendente encontrada.</p>`;
    } else {
        pendingTransfersContainer.innerHTML = tipos.map(tipo => {
            const units = Object.keys(groupedTransfers[tipo]).sort();
            const unitsHtml = units.map(unit => {
                const items = groupedTransfers[tipo][unit];
                const itemsHtml = items.map(item => {
                    const giapItem = giapMap.get(item.Tombamento.trim()); // Busca novamente para garantir
                    const giapUnitName = giapItem ? giapItem.Unidade : 'N/A';
                    return `<div class="p-3 border-t text-sm flex justify-between items-center">
                                <div>
                                    <label class="flex items-center">
                                        <input type="checkbox" class="h-4 w-4 rounded border-gray-300 transfer-item-checkbox" data-id="${item.id}" data-giap-unit="${escapeHtml(giapUnitName)}">
                                        <span class="ml-3"><strong>${escapeHtml(item.Descrição)}</strong> (T: ${escapeHtml(item.Tombamento)})</span>
                                    </label>
                                </div>
                                <div class="text-right">
                                    <p class="text-xs text-slate-500">Destino na Planilha</p>
                                    <p class="font-semibold text-red-600">${escapeHtml(giapUnitName)}</p>
                                </div>
                            </div>`;
                }).join('');

                return `<details class="bg-white rounded-lg shadow-sm border mt-2">
                            <summary class="p-4 font-semibold cursor-pointer flex justify-between items-center hover:bg-slate-50">
                                <span>${escapeHtml(unit)}</span>
                                <span class="text-sm font-bold text-red-600 bg-red-100 px-2 py-1 rounded-full">${items.length} ${items.length > 1 ? 'itens' : 'item'}</span>
                            </summary>
                            <div class="px-4 pb-2 border-t">
                                <div class="py-2 flex justify-between items-center">
                                    <label class="flex items-center text-sm font-medium"><input type="checkbox" class="h-4 w-4 mr-2 select-all-in-unit">Selecionar Todos</label>
                                    <div class="flex gap-2">
                                        <button class="keep-selected-btn text-xs bg-yellow-100 text-yellow-700 px-3 py-1 rounded-md hover:bg-yellow-200">Manter na Unidade</button>
                                        <button class="transfer-selected-btn text-xs bg-blue-100 text-blue-700 px-3 py-1 rounded-md hover:bg-blue-200">Transferir Selecionados</button>
                                    </div>
                                </div>
                                ${itemsHtml}
                            </div>
                        </details>`;
            }).join('');

            return `<div class="mb-4">
                        <h3 class="text-lg font-bold text-slate-700 p-2 bg-slate-200 rounded-t-lg">${tipo}</h3>
                        ${unitsHtml}
                    </div>`;
        }).join('');
    }
}

// parsePtBrDate, populateNfTab, renderNfList, populateGiapTab,
// populateImportAndReplaceTab, populateReconciliationTab, renderList,
// getGlobalLeftovers, getConciliationData, handleSelect, updateImportButton,
// clearGiapImportSelection, addLinkToCreate, renderCreatedLinks,
// renderConciliationLists, openDescriptionChoiceModal, closeDescriptionChoiceModal,
// renderItensATombar, populateSobrantesTab, getFilteredSobrantes,
// renderSobrantesConciliation, findBestMatchForItem, renderEditByDescPreview
// ... (Colar o restante das funções originais aqui, verificando se os IDs dos elementos ainda são válidos)

// --- Handlers ---
// (Colar todos os handlers originais aqui, como handleSaveMapping, handleTransferAction, etc.)
// --- FIM: SEÇÃO ORIGINAL MANTIDA ---


// --- INICIALIZAÇÃO GERAL ---
document.addEventListener('DOMContentLoaded', () => {
    initDomElements(); // Cache DOM elements first

    // Adiciona listener de autenticação APRIMORADO
    addAuthListener(user => {
        if (!authReady) {
            // Este é o primeiro callback, define o estado inicial
            authReady = true;
            console.log("Auth state initialized.");
             // Garante que o estado visual inicial seja 'não logado' até a confirmação
             domCache.userEmailEdit.textContent = 'Verificando...';
             domCache.authGate.classList.remove('hidden'); // Mostra o bloqueio inicialmente
             domCache.loadingScreen.classList.add('hidden'); // Esconde o loading
        }

         // Pequeno delay para dar tempo ao Firebase de confirmar o estado
         setTimeout(() => {
            const currentUser = auth.currentUser; // Pega o estado atualizado
             if (currentUser) {
                 domCache.userEmailEdit.textContent = currentUser.email;
                 domCache.authGate.classList.add('hidden'); // Esconde o bloqueio
                 domCache.loadingScreen.classList.remove('hidden'); // Mostra carregando dados
                 domCache.feedbackStatus.textContent = "Usuário autenticado. Carregando dados...";
                 if (!dataLoaded) {
                     loadData(false); // Carrega os dados APENAS se logado e dados não carregados
                 } else {
                     domCache.loadingScreen.classList.add('hidden'); // Esconde o loading se dados já estavam carregados
                     // Se dados já carregados, inicializa a aba ativa
                      const currentActiveTab = document.querySelector('#edit-nav .nav-btn.active')?.dataset.tab || 'edicao';
                      initializeTabContent(currentActiveTab);
                 }
             } else {
                 domCache.userEmailEdit.textContent = 'Não logado';
                 domCache.authGate.classList.remove('hidden'); // Mostra o bloqueio
                 domCache.loadingScreen.classList.add('hidden'); // Esconde o carregando
                 // Coloca a mensagem de erro dentro do authGate, não no loadingScreen
                 const authGateMessage = `<div class="flex items-center justify-center h-screen"><div class="text-center p-8 bg-white rounded-lg shadow-xl"><h2 class="text-2xl font-bold text-red-600 mb-4">Acesso Negado</h2><p>Você precisa estar logado para acessar esta página.</p><p class="mt-2 text-sm">Volte para a página principal para fazer o login.</p></div></div>`;
                 domCache.authGate.innerHTML = authGateMessage;

             }
         }, 500); // Aumenta um pouco o delay se necessário


    });

    // Listeners de Navegação (Lazy Loading)
    domCache.navButtons.forEach(button => {
        button.addEventListener('click', (e) => {
            const tabName = e.currentTarget.dataset.tab;
            // Troca visual da aba ativa
            domCache.navButtons.forEach(btn => btn.classList.toggle('active', btn.dataset.tab === tabName));
            // Mostra/Esconde painéis de conteúdo
            domCache.contentPanes.forEach(pane => {
                 // Verifica se o ID do painel termina com o nome da aba (considerando prefixo 'content-')
                 const paneId = pane.id || '';
                 pane.classList.toggle('hidden', !paneId.startsWith(`content-${tabName}`));
            });


            // Inicializa o conteúdo da aba SE necessário e SE logado/dados carregados
            if (authReady && auth.currentUser && dataLoaded) {
                initializeTabContent(tabName);
            } else if (authReady && !auth.currentUser) {
                 console.log("User not logged in, cannot initialize tab content.");
                 showNotification("Faça login para acessar esta aba.", "warning");
            } else {
                 console.log("Auth or data not ready, delaying tab initialization.");
                  showNotification("Aguarde o carregamento dos dados...", "info");
            }
        });
    });

    // Adiciona listeners para os modais (importante!)
    document.getElementById('desc-choice-cancel-btn')?.addEventListener('click', handleDescChoiceCancel);
    document.getElementById('desc-choice-keep-btn')?.addEventListener('click', handleDescChoiceKeep);
    document.getElementById('desc-choice-update-btn')?.addEventListener('click', handleDescChoiceUpdate);

    // Adiciona listener para fechar modais genéricos
    document.addEventListener('click', (e) => {
        // Modal de Exclusão (Novo)
        const deleteModalEdit = document.getElementById('delete-confirm-modal-edit');
        if (deleteModalEdit && !deleteModalEdit.classList.contains('hidden')) {
            if (e.target.matches('.modal-overlay') || e.target.closest('#cancel-delete-edit-btn')) {
                 closeDeleteConfirmModal();
            }
        }
         // Modal de Escolha de Descrição
        const descChoiceModal = document.getElementById('desc-choice-modal');
         if (descChoiceModal && !descChoiceModal.classList.contains('hidden')) {
            if (e.target.matches('.modal-overlay') || e.target.closest('#desc-choice-cancel-btn')) {
                 handleDescChoiceCancel(); // Usa o handler para limpar seleção
            }
        }

        // Adicionar fechamento para outros modais se necessário,
        // usando seus respectivos botões/overlays e funções de fechamento
    });

    // --- Adiciona listeners que dependem do DOM da Aba Otimizada ---
    // (Movidos de initEditableInventoryTab para cá, pois dependem de initDomElements)
    const debouncedFilter = debounce(applyFiltersAndPaginate, DEBOUNCE_DELAY);
    document.getElementById('edit-filter-tipo')?.addEventListener('change', debouncedFilter);
    document.getElementById('edit-filter-unidade')?.addEventListener('change', debouncedFilter);
    document.getElementById('edit-filter-estado')?.addEventListener('change', debouncedFilter);
    document.getElementById('edit-filter-descricao')?.addEventListener('input', debouncedFilter);

    domCache.prevPageBtn?.addEventListener('click', () => goToPage(currentPage - 1));
    domCache.nextPageBtn?.addEventListener('click', () => goToPage(currentPage + 1));
    domCache.saveAllChangesBtn?.addEventListener('click', saveAllChanges);

    document.getElementById('force-refresh-btn')?.addEventListener('click', async () => {
        if (dirtyItems.size > 0 && !confirm(`Você tem ${dirtyItems.size} alterações não salvas. Deseja recarregar?`)) return;
        dirtyItems.clear(); // Limpa alterações pendentes
        initializedTabs.clear(); // Reseta abas inicializadas
        dataLoaded = false; // Força recarregamento completo
        await loadData(true); // Recarrega os dados do servidor
        // A aba 'edicao' será reinicializada automaticamente pelo loadData -> initializeTabContent
    });
    document.getElementById('logout-btn')?.addEventListener('click', () => { handleLogout(); window.location.href = 'index.html'; });

    document.getElementById('confirm-delete-edit-btn')?.addEventListener('click', confirmDeleteItems);
    document.getElementById('cancel-delete-edit-btn')?.addEventListener('click', closeDeleteConfirmModal);


}); // Fim do DOMContentLoaded

