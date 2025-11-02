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
let dataLoaded = false; // Flag para indicar que os dados principais foram carregados
const initializedTabs = new Set(); // Conjunto para rastrear abas já inicializadas
const loadedNfDetails = new Set(); // NOVO: Para rastrear detalhes de NF carregados

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
    editFilterTipo: null, // NOVO: Cache dos filtros
    editFilterUnidade: null, // NOVO: Cache dos filtros
    // Gerais
    loadingScreen: null,
    authGate: null, // Agora é o overlay de "Acesso Negado"
    appWrapper: null, // NOVO: O wrapper de toda a aplicação
    feedbackStatus: null,
    navButtons: null,
    contentPanes: null,
    userEmailEdit: null,
    nfContainer: null // NOVO: Cache container NF
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
    domCache.editFilterTipo = document.getElementById('edit-filter-tipo'); // NOVO
    domCache.editFilterUnidade = document.getElementById('edit-filter-unidade'); // NOVO
    // Gerais
    domCache.loadingScreen = document.getElementById('loading-or-error-screen');
    domCache.authGate = document.getElementById('auth-gate'); // Div de overlay "Acesso Negado"
    domCache.appWrapper = document.getElementById('app-wrapper'); // Div que envolve o app
    domCache.feedbackStatus = document.getElementById('feedback-status');
    domCache.navButtons = document.querySelectorAll('#edit-nav .nav-btn');
    domCache.contentPanes = document.querySelectorAll('main > div[id^="content-"]');
    domCache.userEmailEdit = document.getElementById('user-email-edit');
    domCache.nfContainer = document.getElementById('notas-fiscais-container'); // NOVO

    console.log("DOM elements cached.");
}

// --- FUNÇÕES UTILITÁRIAS (Normalização, Parse, etc.) ---
const normalizeTombo = (tombo) => {
    if (tombo === undefined || tombo === null || String(tombo).trim() === '') return '';
    let str = String(tombo).trim();
    if (/^0?\d+(\.0)?$/.test(str)) return String(parseInt(str, 10));
    return str;
};

function parseEstadoEOrigem(texto) {
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

// Função auxiliar para obter o caminho da coleção (Duplicado aqui para evitar erro de import circular)
const getCollectionPath = (collectionName) => `artifacts/${auth.currentUser?.uid ? 'public' : 'default-app-id'}/data/${collectionName}`;


// --- FUNÇÕES DE SIMILARIDADE E IA ---
async function carregarPadroesConciliacao() {
    // MUDANÇA: Usa a coleção correta no Firebase
    if (!auth.currentUser) return; // Não carrega se não estiver autenticado (nem anonimamente)
    try {
        const q = query(
            collection(db, getCollectionPath('padroesConciliacao')),
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
    // MUDANÇA: Usa a coleção correta no Firebase
    if (!auth.currentUser || auth.currentUser.isAnonymous) return;
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
        await addDoc(collection(db, getCollectionPath('padroesConciliacao')), padrao);
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
    const activeTabEl = document.querySelector('#content-conciliar .sub-nav-btn.active');
    const activeSubTab = activeTabEl ? activeTabEl.dataset.subtabConciliar : 'conciliacao_unidade';
    const isSobrantesTab = activeSubTab === 'conciliacao_sobras';

    const giapListId = isSobrantesTab ? 'sobras-giap-list' : 'giap-list';
    const context = isSobrantesTab ? 'sobras' : 'default';

    if (!giapSourceItems || giapSourceItems.length === 0) {
        renderList(giapListId, [], 'TOMBAMENTO', 'Descrição', null, context);
        return;
    }

    const systemDesc = `${systemItem.Descrição || ''} ${systemItem.Fornecedor || ''}`.trim();
    const scoredItems = giapSourceItems.map(giapItem => {
        const giapDesc = `${giapItem.Descrição || ''} ${giapItem.Espécie || ''} ${giapItem['Nome Fornecedor'] || ''}`.trim();
        let baseScore = calculateSimilarity(systemDesc, giapDesc);
        // Ajuste de pontuação baseado no fornecedor
        if (systemItem.Fornecedor && systemItem.Fornecedor !== '-' && giapItem['Nome Fornecedor'] && giapItem['Nome Fornecedor'] !== '-') {
             const fornNormSys = normalizeStr(systemItem.Fornecedor);
             const fornNormGiap = normalizeStr(giapItem['Nome Fornecedor']);
             // Verificação mais flexível (contém partes significativas)
             const fornPartsSys = fornNormSys.split(' ').filter(p => p.length > 3);
             const fornPartsGiap = fornNormGiap.split(' ').filter(p => p.length > 3);
             const commonParts = fornPartsSys.filter(p => fornPartsGiap.includes(p));
             if (commonParts.length > 0) {
                 baseScore += 0.10 * commonParts.length; // Bônus por partes em comum
             }
        }
        return { item: giapItem, baseScore: Math.min(baseScore, 1.0), bonusScore: 0 };
    });

    // Aplica aprendizado dos padrões
    if (padroesConciliacao.length > 0) {
        padroesConciliacao.forEach(padrao => {
            const similaridadeComPadrao = calculateSimilarity(systemDesc, `${padrao.descricaoSistema} ${padrao.fornecedorSistema}`);
            if (similaridadeComPadrao > 0.7) { // Limiar de similaridade com o padrão
                scoredItems.forEach(scored => {
                    const giapDescCompleta = `${scored.item.Descrição || ''} ${scored.item.Espécie || ''} ${scored.item['Nome Fornecedor'] || ''}`;
                    const similaridadeComPadraoGiap = calculateSimilarity(giapDescCompleta, `${padrao.descricaoGIAP} ${padrao.fornecedorGIAP}`);
                    if (similaridadeComPadraoGiap > 0.6) { // Limiar de similaridade GIAP
                        // Boost baseado na força da correspondência com o padrão
                        const boost = similaridadeComPadrao * similaridadeComPadraoGiap * 0.25; // Aumentei um pouco o boost
                        scored.bonusScore += boost;
                         console.log(`Applied boost ${boost.toFixed(3)} to ${scored.item.TOMBAMENTO} based on pattern match.`);
                    }
                });
            }
        });
    }


    scoredItems.forEach(scored => { scored.finalScore = Math.min(scored.baseScore + scored.bonusScore, 1.0); });
    scoredItems.sort((a, b) => b.finalScore - a.finalScore);
    const topScore = scoredItems.length > 0 ? scoredItems[0].finalScore : 0;
    const suggestionMap = new Map(scoredItems.map(si => [si.item.TOMBAMENTO, si.finalScore]));

    // Log para depuração
     console.log(`Top suggestions for "${systemItem.Descrição}":`);
     scoredItems.slice(0, 5).forEach(si => console.log(`  - ${si.item.TOMBAMENTO}: ${si.finalScore.toFixed(3)} (Base: ${si.baseScore.toFixed(3)}, Bonus: ${si.bonusScore.toFixed(3)}) - ${si.item.Descrição || si.item.Espécie}`));


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
        .filter(match => match.score > 0.65) // Limiar de similaridade
        .sort((a, b) => b.score - a.score);

    if (potentialMatches.length > 0) {
        // Verifica ambiguidade
        if (potentialMatches.length > 1 && (potentialMatches[0].score - potentialMatches[1].score) < 0.1) {
            // Se os scores são muito próximos, considera ambíguo
             console.log(`Ambiguous match for "${pastedItem.descricao}": `, potentialMatches.slice(0,3));
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
    // Assegura que a tela de loading esteja visível
    domCache.loadingScreen.classList.remove('hidden');
    domCache.feedbackStatus.textContent = 'Verificando cache de dados...';
    console.log("Verificando cache..."); // LOG ADICIONAL

    const metadata = await idb.metadata.get('lastFetch');
    const isCacheStale = !metadata || (Date.now() - metadata.timestamp > CACHE_DURATION_MS);

    if (!forceRefresh && !isCacheStale) {
        console.log("Cache válido. Carregando do IndexedDB..."); // LOG ADICIONAL
        domCache.feedbackStatus.textContent = 'Carregando dados do cache local...';
        try {
            [fullInventory, giapInventory, unitMapping, customGiapUnits, reconciledUnits] = await Promise.all([
                idb.patrimonio.toArray(),
                idb.giap.toArray(),
                loadUnitMappingFromFirestore(),
                loadCustomGiapUnits(),
                loadReconciledUnits()
            ]);
            console.log(`Dados carregados do cache: Inventário(${fullInventory.length}), GIAP(${giapInventory.length})`); // LOG ADICIONAL
            showNotification('Dados carregados do cache.', 'info');
        } catch (cacheError) {
             console.error("Erro ao carregar do cache:", cacheError);
             showNotification('Erro ao ler o cache local.', 'error');
             // Forçar busca do servidor se o cache falhar
             return loadData(true);
        }
    } else {
        console.log("Cache inválido ou refresh forçado. Buscando do servidor..."); // LOG ADICIONAL
        domCache.feedbackStatus.textContent = 'Buscando dados atualizados do servidor...';
        try {
            [fullInventory, giapInventory, unitMapping, customGiapUnits, reconciledUnits] = await Promise.all([
                loadFirebaseInventory(),
                loadGiapInventory(),
                loadUnitMappingFromFirestore(),
                loadCustomGiapUnits(),
                loadReconciledUnits()
            ]);
            console.log(`Dados carregados do servidor: Inventário(${fullInventory.length}), GIAP(${giapInventory.length})`); // LOG ADICIONAL
            await idb.transaction('rw', idb.patrimonio, idb.giap, idb.metadata, async () => {
                await idb.patrimonio.clear(); await idb.patrimonio.bulkAdd(fullInventory);
                await idb.giap.clear(); await idb.giap.bulkAdd(giapInventory);
                await idb.metadata.put({ key: 'lastFetch', timestamp: Date.now() });
            });
            console.log("Cache atualizado no IndexedDB."); // LOG ADICIONAL
            showNotification('Dados atualizados com sucesso!', 'success');
        } catch (error) {
            console.error("Erro ao buscar dados do servidor:", error); // LOG ADICIONAL
            domCache.loadingScreen.innerHTML = `<div class="text-center"><h2 class="text-xl font-bold text-red-600">Erro ao Carregar Dados</h2><p>${error.message}</p></div>`;
            showNotification('Erro ao carregar dados do servidor.', 'error');
            dataLoaded = false;
            // Tenta carregar do cache como fallback (MELHORADO)
             try {
                 console.log("Tentando fallback para o cache..."); // LOG ADICIONAL
                 domCache.feedbackStatus.textContent = 'Falha ao buscar. Tentando carregar do cache...';
                [fullInventory, giapInventory] = await Promise.all([ // Só carrega o essencial do cache
                    idb.patrimonio.toArray(),
                    idb.giap.toArray(),
                ]);
                 // Carrega config do Firestore mesmo no fallback
                 [unitMapping, customGiapUnits, reconciledUnits] = await Promise.all([
                    loadUnitMappingFromFirestore(),
                    loadCustomGiapUnits(),
                    loadReconciledUnits()
                 ]);

                 if (fullInventory.length > 0) {
                     console.log(`Fallback para cache bem-sucedido: Inventário(${fullInventory.length}), GIAP(${giapInventory.length})`); // LOG ADICIONAL
                     showNotification('Dados carregados do cache (fallback).', 'warning');
                 } else {
                     throw new Error("Cache vazio ou inacessível."); // Força o erro se o cache também falhar
                 }
            } catch (cacheError) {
                 console.error("Erro ao carregar dados (Servidor e Cache Fallback):", error, cacheError); // LOG ADICIONAL
                 domCache.loadingScreen.innerHTML = `<div class="text-center"><h2 class="text-xl font-bold text-red-600">Erro Crítico</h2><p>Não foi possível carregar os dados do servidor nem do cache local. Verifique sua conexão e tente recarregar a página.</p><p class="text-sm mt-2">${error.message}</p></div>`;
                 return; // Impede a continuação
            }
        }
    }

    // Processamento essencial dos dados (verificações adicionadas)
    if (giapInventory && giapInventory.length > 0) {
        giapMap = new Map(giapInventory
            .filter(item => item && normalizeStr(item.Status).includes(normalizeStr('Disponível')))
            .map(item => [normalizeTombo(item['TOMBAMENTO']), item])
        );
        giapMapAllItems = new Map(giapInventory.map(item => item ? [normalizeTombo(item['TOMBAMENTO']), item] : null).filter(Boolean));
        console.log(`GIAP Maps criados: giapMap(${giapMap.size}), giapMapAllItems(${giapMapAllItems.size})`); // LOG ADICIONAL
    } else {
         console.warn("giapInventory está vazio ou inválido. Maps não foram criados.");
         giapMap = new Map();
         giapMapAllItems = new Map();
    }


    normalizedSystemUnits.clear();
    if (fullInventory && fullInventory.length > 0) {
        fullInventory.forEach(item => {
            if (item && item.Unidade) {
                const normalized = normalizeStr(item.Unidade);
                if (!normalizedSystemUnits.has(normalized)) {
                    normalizedSystemUnits.set(normalized, item.Unidade.trim());
                }
            }
        });
        console.log(`Unidades do sistema normalizadas: ${normalizedSystemUnits.size}`); // LOG ADICIONAL
    } else {
         console.warn("fullInventory está vazio ou inválido. Unidades do sistema não normalizadas.");
    }


    // Chama a função que foi movida para cima
    await carregarPadroesConciliacao();

    dataLoaded = true;
    domCache.feedbackStatus.textContent = `Pronto. ${fullInventory?.length || 0} itens carregados.`; // Usar fallback
    domCache.loadingScreen.classList.add('hidden'); // Esconde o loading AQUI
    console.log("Data loading complete. Hidden loading screen."); // LOG ADICIONAL

    // **MOVER** a exibição do appWrapper para depois do processamento
    if (domCache.appWrapper) {
         domCache.appWrapper.classList.remove('hidden');
         console.log("App wrapper displayed."); // LOG ADICIONAL
    } else {
         console.error("App wrapper not found in DOM cache!");
    }

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
    // Adiciona log para verificar se os dados estão presentes
    console.log(`Initializing tab content for: ${tabName}. Inventory count: ${fullInventory?.length || 0}`);

    if (initializedTabs.has(tabName)) {
        console.log(`Tab ${tabName} already initialized. Re-rendering (if applicable)...`); // LOG ADICIONAL
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

    console.log(`Initializing tab for the first time: ${tabName}`); // LOG ADICIONAL
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

// --- FIM: FUNÇÕES DE INICIALIZAÇÃO POR ABA ---


// --- FUNÇÕES DE INICIALIZAÇÃO POR ABA ---

function updateUnidadeFilterOptions() {
    if (!domCache.editFilterTipo || !domCache.editFilterUnidade) return;

    const selectedTipo = domCache.editFilterTipo.value;
    const currentSelectedUnidade = domCache.editFilterUnidade.value;

    let unidadesOptions = ['<option value="">Todas as Unidades</option>'];

    if (selectedTipo) {
        const unidadesDoTipo = [...new Set((fullInventory || [])
            .filter(i => i.Tipo === selectedTipo)
            .map(i => i.Unidade))]
            .filter(Boolean)
            .sort();
        unidadesOptions.push(...unidadesDoTipo.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`));
        domCache.editFilterUnidade.disabled = false;
    } else {
        const todasUnidades = [...new Set((fullInventory || []).map(i => i.Unidade))]
            .filter(Boolean)
            .sort();
        unidadesOptions.push(...todasUnidades.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`));
        domCache.editFilterUnidade.disabled = false;
    }

    domCache.editFilterUnidade.innerHTML = unidadesOptions.join('');

    if (domCache.editFilterUnidade.querySelector(`option[value="${currentSelectedUnidade}"]`)) {
        domCache.editFilterUnidade.value = currentSelectedUnidade;
    } else {
        domCache.editFilterUnidade.value = "";
    }
}


function initEditableInventoryTab() {
    console.log("Initializing Editable Inventory Tab");
    const tipos = [...new Set((fullInventory || []).map(i => i.Tipo))].filter(Boolean).sort();

    if (domCache.editFilterTipo) {
        domCache.editFilterTipo.innerHTML = '<option value="">Todos os Tipos</option>' + tipos.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');
    }

    updateUnidadeFilterOptions();
    if (domCache.editFilterTipo) {
        domCache.editFilterTipo.addEventListener('change', () => {
             console.log("Filtro de tipo alterado.");
            updateUnidadeFilterOptions();
            applyFiltersAndPaginate();
        });
    }


    applyFiltersAndPaginate();
    setupEventDelegation();
}

function initUnitMappingTab() {
    console.log("Initializing Unit Mapping Tab");
    populateUnitMappingTab();
    document.getElementById('map-filter-tipo')?.addEventListener('change', updateSystemUnitOptions);
    document.getElementById('map-system-unit-select')?.addEventListener('change', updateGiapUnitOptions);
    document.getElementById('map-giap-filter')?.addEventListener('input', debounce(updateGiapUnitOptions, 300));
    document.getElementById('save-mapping-btn')?.addEventListener('click', handleSaveMapping);
    document.getElementById('saved-mappings-container')?.addEventListener('click', handleDeleteMapping);
}

function initReconciliationTab() {
    console.log("Initializing Reconciliation Tab");
    populateReconciliationTab();
    document.getElementById('filter-tipo')?.addEventListener('change', handleConciliationTypeChange);
    document.getElementById('load-conciliar')?.addEventListener('click', handleLoadConciliation);
    const debouncedRenderConciliation = debounce(renderConciliationLists, 300);
    document.getElementById('system-list-filter')?.addEventListener('input', debouncedRenderConciliation);
    document.getElementById('giap-list-filter')?.addEventListener('input', debouncedRenderConciliation);
    document.getElementById('clear-selections')?.addEventListener('click', handleClearConciliationSelections);
    document.getElementById('save-links')?.addEventListener('click', () => savePendingLinks('unidade').then(handleSaveLinksResult));
    document.getElementById('finish-reconciliation-btn')?.addEventListener('click', handleFinishReconciliation);
    document.getElementById('created-links')?.addEventListener('click', handleDeleteCreatedLink);
    document.getElementById('import-giap-btn')?.addEventListener('click', handleImportGiapItems);

    const subNavButtonsConciliar = document.querySelectorAll('#content-conciliar .sub-nav-btn');
    subNavButtonsConciliar.forEach(button => {
        button.addEventListener('click', handleConciliationSubTabSwitch);
    });

    document.getElementById('load-sobras-conciliar')?.addEventListener('click', renderSobrantesConciliation);
    const debouncedRenderSobrantes = debounce(renderSobrantesConciliation, 300);
    document.getElementById('sobras-system-list-filter')?.addEventListener('input', debouncedRenderSobrantes);
    document.getElementById('sobras-giap-list-filter')?.addEventListener('input', debouncedRenderSobrantes);
    document.getElementById('sobras-giap-type-filter')?.addEventListener('change', debouncedRenderSobrantes);
    document.getElementById('sobras-save-links')?.addEventListener('click', () => savePendingLinks('sobras').then(handleSaveLinksResultSobras));
    document.getElementById('sobras-clear-selections')?.addEventListener('click', handleClearSobrantesSelections);
    document.getElementById('sobras-created-links')?.addEventListener('click', handleDeleteCreatedLinkSobras);

    document.getElementById('tombar-filter-tipo')?.addEventListener('change', handleTombarFilterChange);
    document.getElementById('tombar-filter-unidade')?.addEventListener('change', renderItensATombar);
    document.getElementById('itens-a-tombar-container')?.addEventListener('click', handleConfirmTombamento);
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
    if(dataLoaded) document.getElementById('suggest-sobrando')?.click();
}

function initPendingTransfersTab() {
    console.log("Initializing Pending Transfers Tab");
    populatePendingTransfersTab();
    document.getElementById('pending-transfers-container')?.addEventListener('click', handleTransferAction);
}

function initImportAndReplaceTab() {
    console.log("Initializing Import/Replace Tab");
    populateImportAndReplaceTab();
     const subNavButtonsImport = document.querySelectorAll('#content-importacao .sub-nav-btn');
     subNavButtonsImport.forEach(button => {
         button.addEventListener('click', handleImportSubTabSwitch);
     });
     document.getElementById('preview-replace-btn')?.addEventListener('click', handlePreviewReplace);
     document.getElementById('replace-confirm-checkbox')?.addEventListener('change', handleReplaceConfirmChange);
     document.getElementById('confirm-replace-btn')?.addEventListener('click', handleConfirmReplace);
     document.getElementById('preview-edit-by-desc-btn')?.addEventListener('click', handlePreviewEditByDesc);
     document.getElementById('edit-by-desc-preview-table-container')?.addEventListener('change', handleEditByDescCheckboxChange);
     document.getElementById('confirm-edit-by-desc-btn')?.addEventListener('click', handleConfirmEditByDesc);
     document.getElementById('mass-transfer-search-btn')?.addEventListener('click', handleMassTransferSearch);
     document.getElementById('mass-transfer-set-all-status')?.addEventListener('change', handleMassTransferSetAllStatus);
     document.getElementById('mass-transfer-confirm-btn')?.addEventListener('click', handleMassTransferConfirm);
     document.getElementById('save-giap-unit-btn')?.addEventListener('click', handleSaveGiapUnit);
}

function initNfTab() {
    console.log("Initializing NF Tab");
    populateNfTab();
    const debouncedRenderNf = debounce(renderNfList, 300);
    document.getElementById('nf-search')?.addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-item-search')?.addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-fornecedor-search')?.addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-tipo-entrada')?.addEventListener('change', renderNfList);
    document.getElementById('nf-status-filter')?.addEventListener('change', renderNfList);
    document.getElementById('nf-date-start')?.addEventListener('change', renderNfList);
    document.getElementById('nf-date-end')?.addEventListener('change', renderNfList);
    document.getElementById('clear-nf-filters-btn')?.addEventListener('click', handleClearNfFilters);
    domCache.nfContainer?.addEventListener('toggle', handleNfDetailsToggle, true);
}

function initGiapTab() {
    console.log("Initializing GIAP Tab");
    populateGiapTab();
}


// --- FIM: FUNÇÕES DE INICIALIZAÇÃO POR ABA ---


// --- INÍCIO: SEÇÃO ULTRA OTIMIZADA (Funções coladas) ---

// --- LÓGICA ADAPTATIVA DE FILTROS ---
function applyFiltersAndPaginate() {
    // Adiciona verificação se os elementos existem
    const tipoEl = domCache.editFilterTipo; // Usa cache
    const unidadeEl = domCache.editFilterUnidade; // Usa cache
    const estadoEl = document.getElementById('edit-filter-estado');
    const descricaoEl = document.getElementById('edit-filter-descricao');

    const tipo = tipoEl ? tipoEl.value : '';
    const unidade = unidadeEl ? unidadeEl.value : '';
    const estado = estadoEl ? estadoEl.value : '';
    const descricao = descricaoEl ? normalizeStr(descricaoEl.value) : '';


    // Detectar se há QUALQUER filtro ativo
    isFiltered = !!(tipo || unidade || estado || descricao);

    // Filtrar inventário (Adicionado fallback para array vazio)
    filteredInventory = (fullInventory || []).filter(item => {
        if (!item) return false; // Segurança extra
        if (tipo && item.Tipo !== tipo) return false;
        if (unidade && item.Unidade !== unidade) return false;
        if (estado && item.Estado !== estado) return false;
        if (descricao && !normalizeStr(item.Descrição || '').includes(descricao)) return false;
        return true;
    });
    console.log(`Filtros aplicados. Itens filtrados: ${filteredInventory.length}`); // LOG ADICIONAL


    // LÓGICA ADAPTATIVA:
    if (isFiltered) {
        showAllItems = true;
        totalPages = 1;
        currentPage = 1;
        console.log("Modo filtrado: mostrando todos os itens."); // LOG ADICIONAL

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
        totalPages = Math.max(1, Math.ceil((filteredInventory?.length || 0) / ITEMS_PER_PAGE_DEFAULT)); // Fallback
        currentPage = Math.min(currentPage, totalPages);
        console.log(`Modo paginado: Página ${currentPage}/${totalPages}`); // LOG ADICIONAL
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
        // Paginação normal (Adicionado fallback para array vazio)
        const start = (currentPage - 1) * ITEMS_PER_PAGE_DEFAULT;
        const end = start + ITEMS_PER_PAGE_DEFAULT;
        itemsToRender = (filteredInventory || []).slice(start, end);
    }
    console.log(`Itens para renderizar na tabela: ${itemsToRender?.length || 0}`); // LOG ADICIONAL


    // Usar DocumentFragment para renderização super rápida
    const fragment = document.createDocumentFragment();

    // Renderizar em lote
    if (itemsToRender && itemsToRender.length > 0) {
        itemsToRender.forEach(item => {
            if (!item || !item.id) { // Checagem extra de segurança
                console.warn("Item inválido encontrado durante a renderização:", item);
                return;
            }
            const itemData = dirtyItems.get(item.id) || item; // Pega dados 'sujos' se existirem
            const tr = document.createElement('tr');
            tr.dataset.id = item.id;
            tr.className = dirtyItems.has(item.id) ? 'edited-row' : '';

            const giapItem = giapMap.get(normalizeTombo(itemData.Tombamento));
            const hasGiap = !!giapItem;
            const tomboReadonly = hasGiap ? 'readonly title="Vinculado ao GIAP"' : '';
            const tomboValue = escapeHtml(itemData.Tombamento || '');

            tr.innerHTML = `
                <td class="px-2 py-1 text-xs whitespace-nowrap">${escapeHtml(itemData.Tipo || '')}</td>
                <td class="px-2 py-1 text-xs whitespace-nowrap">${escapeHtml(itemData.Unidade || '')}</td>
                <td class="px-2 py-1 text-xs relative"> <!-- Adicionado relative -->
                    <input type="text" class="w-full p-1 border rounded text-xs editable-field"
                           data-field="Tombamento" data-id="${item.id}"
                           value="${tomboValue}" ${tomboReadonly}>
                    <!-- NOVO Botão Sync -->
                    ${!hasGiap ? `
                    <button class="absolute right-1 top-1/2 transform -translate-y-1/2 p-0.5 text-blue-500 hover:text-blue-700 sync-tombo-btn"
                            data-sync-id="${item.id}" title="Buscar dados do GIAP para este tombo">
                        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" fill="currentColor" class="pointer-events-none" viewBox="0 0 16 16">
                          <path fill-rule="evenodd" d="M8 3a5 5 0 1 0 4.546 2.914.5.5 0 0 1 .908-.417A6 6 0 1 1 8 2z"/>
                          <path d="M8 4.466V.534a.25.25 0 0 1 .41-.192l2.36 1.966c.12.1.12.284 0 .384L8.41 4.658A.25.25 0 0 1 8 4.466zM12.5 10a.5.5 0 0 1-.5.5h-4a.5.5 0 0 1 0-1h4a.5.5 0 0 1 .5.5m-5-2.5a.5.5 0 0 1 .5-.5h5a.5.5 0 0 1 0 1h-5a.5.5 0 0 1-.5-.5m-5 5a.5.5 0 0 1 .5-.5h5a.5.5 0 0 1 0 1h-5a.5.5 0 0 1-.5-.5"/>
                        </svg>
                    </button>
                    ` : ''}
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
    } else {
        // Exibe mensagem se não houver itens para renderizar
        const tr = document.createElement('tr');
        tr.innerHTML = `<td colspan="9" class="text-center p-10 text-slate-500">Nenhum item encontrado${isFiltered ? ' com os filtros aplicados' : ''}.</td>`;
        fragment.appendChild(tr);
    }


    // Limpar e inserir de uma vez (super rápido)
    requestAnimationFrame(() => {
        if (domCache.editTableBody) { // Checa se ainda existe (pode ter mudado de aba)
             domCache.editTableBody.innerHTML = '';
             domCache.editTableBody.appendChild(fragment);
        }
    });


    const renderTime = (performance.now() - startTime).toFixed(0);
    console.log(`✅ ${itemsToRender?.length || 0} itens renderizados em ${renderTime}ms (Render Function)`);
}

function updatePaginationControls() {
    if (!domCache.pageInfo) return;

    const inventoryLength = filteredInventory?.length || 0; // Fallback

    if (showAllItems) {
        // Modo filtrado - mostrar todos
        domCache.pageInfo.innerHTML = `
            <span class="text-green-600 font-semibold">
                📋 Mostrando TODOS os ${inventoryLength} itens filtrados
            </span>
            ${dirtyItems.size > 0 ? `<span class="text-orange-600 ml-3">✏️ ${dirtyItems.size} alterações pendentes</span>` : ''}
        `;
    } else {
        // Modo paginado
        const start = inventoryLength === 0 ? 0 : (currentPage - 1) * ITEMS_PER_PAGE_DEFAULT + 1;
        const end = Math.min(currentPage * ITEMS_PER_PAGE_DEFAULT, inventoryLength);

        domCache.pageInfo.innerHTML = `
            Mostrando ${start}-${end} de ${inventoryLength} itens (Página ${currentPage}/${totalPages})
            ${dirtyItems.size > 0 ? `<span class="text-orange-600 ml-3">✏️ ${dirtyItems.size} alterações</span>` : ''}
        `;

        if(domCache.prevPageBtn) domCache.prevPageBtn.disabled = currentPage === 1;
        if(domCache.nextPageBtn) domCache.nextPageBtn.disabled = currentPage === totalPages;
    }

    // Botão salvar
    if(domCache.saveAllChangesBtn) {
        // MUDANÇA: Desabilita se for anônimo, independente do dirtyItems
        const isAnonymous = auth.currentUser ? auth.currentUser.isAnonymous : true;
        const isDisabled = dirtyItems.size === 0 || isAnonymous;

        domCache.saveAllChangesBtn.disabled = isDisabled;
        domCache.saveAllChangesBtn.title = isAnonymous ? "Faça login para salvar alterações" : (dirtyItems.size === 0 ? "Nenhuma alteração pendente" : "");

        if (dirtyItems.size > 0 && !isAnonymous) {
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
    // MUDANÇA: Bloqueia a edição no input se for anônimo
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        // Reverte o valor do campo para o original
        const itemId = e.target.dataset.id;
        const fieldName = e.target.dataset.field;
        const originalItem = fullInventory.find(i => i.id === itemId);
        if (originalItem) {
             e.target.value = originalItem[fieldName] || '';
        }
        return;
    }

    const field = e.target;
    if (!field.classList.contains('editable-field')) return;

    const itemId = field.dataset.id;
    const fieldName = field.dataset.field;
    let newValue = field.value; // NÂO usar .trim() aqui

    const item = fullInventory.find(i => i.id === itemId);
    if (!item) return;

    // Obtém o estado atual (seja o original ou já modificado)
    const currentItemState = dirtyItems.get(itemId) || { ...item }; // Cria cópia se não estiver sujo

    // Verifica se houve mudança real
    const currentValueStr = (item[fieldName] === null || item[fieldName] === undefined) ? '' : String(item[fieldName]);
    const newValueStr = (newValue === null || newValue === undefined) ? '' : String(newValue);

    // Atualiza o estado sujo APENAS se o novo valor for DIFERENTE do ORIGINAL
    if (newValueStr !== currentValueStr) {
        const updatedItem = { ...currentItemState, [fieldName]: newValue };
        dirtyItems.set(itemId, updatedItem);
        field.closest('tr').classList.add('edited-row');
        console.log(`Item ${itemId} marked dirty. Field: ${fieldName}, New Value: '${newValue}' (Original: '${currentValueStr}')`);
    } else {
        // Se voltou ao valor ORIGINAL, remove a sujeira DESSE campo
        if (dirtyItems.has(itemId)) {
             const dirtyData = dirtyItems.get(itemId);
             // Remove o campo do objeto sujo
             delete dirtyData[fieldName];
             // Verifica se ainda há outros campos sujos
             const originalItem = fullInventory.find(i => i.id === itemId);
             const otherDirtyFieldsExist = Object.keys(dirtyData).some(key =>
                 key !== 'id' && // Ignora id
                 String(dirtyData[key]) !== ((originalItem[key] === null || originalItem[key] === undefined) ? '' : String(originalItem[key]))
             );

             if (!otherDirtyFieldsExist) {
                 // Se não há mais campos sujos, remove o item do Map
                 dirtyItems.delete(itemId);
                 field.closest('tr').classList.remove('edited-row');
                 console.log(`Item ${itemId} reverted to original state. Removed from dirty list.`);
             } else {
                 // Atualiza o Map com o objeto sem o campo revertido
                 dirtyItems.set(itemId, dirtyData);
                 field.closest('tr').classList.add('edited-row'); // Mantém amarelo se houver outras alterações
                 console.log(`Field ${fieldName} reverted on item ${itemId}, but other changes remain.`);
             }
        } else {
             // Se não estava no dirtyItems, apenas remove a classe (caso tenha sido adicionada por sync)
              field.closest('tr').classList.remove('edited-row');
        }
    }
    updatePaginationControls();
}


// Handler separado para click (AGORA INCLUI SYNC)
function handleTableClick(e) {
    const deleteBtn = e.target.closest('.delete-item-btn');
    const syncBtn = e.target.closest('.sync-tombo-btn'); // NOVO

    if (deleteBtn) {
         // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
        if (auth.currentUser?.isAnonymous) {
            showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
            return;
        }
        const itemId = deleteBtn.dataset.id;
        openDeleteConfirmModal([itemId]);
    } else if (syncBtn) { // NOVO Bloco
         // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
        if (auth.currentUser?.isAnonymous) {
            showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
            return;
        }
        const itemId = syncBtn.dataset.syncId;
        handleSyncTombo(itemId, syncBtn); // Chama a nova função de sync
    }
}

// **NOVA Função:** Lógica para sincronizar com GIAP
async function handleSyncTombo(itemId, buttonEl) {
    const row = buttonEl.closest('tr');
    if (!row) return;
    const tomboInput = row.querySelector('input[data-field="Tombamento"]');
    const descInput = row.querySelector('input[data-field="Descrição"]');
    const fornInput = row.querySelector('input[data-field="Fornecedor"]');

    if (!tomboInput || !descInput || !fornInput) {
        console.error("Não foi possível encontrar os campos na linha para sincronizar.");
        return;
    }

    const tomboValueRaw = tomboInput.value;
    const tomboValueNorm = normalizeTombo(tomboValueRaw);

    if (!tomboValueNorm || tomboValueNorm.toLowerCase() === 's/t') {
        showNotification("Digite um número de tombamento válido para buscar.", "warning");
        return;
    }

    // Adiciona um spinner ao botão
    buttonEl.disabled = true;
    buttonEl.innerHTML = '<div class="btn-spinner" style="width: 12px; height: 12px; border-width: 2px;"></div>';

    // Busca no GIAP (usando giapMapAllItems para pegar todos os status)
    const giapItem = giapMapAllItems.get(tomboValueNorm);

    if (giapItem) {
        console.log(`GIAP data found for tombo ${tomboValueNorm}:`, giapItem);
        const newDesc = giapItem.Descrição || giapItem.Espécie || '';
        const newForn = giapItem['Nome Fornecedor'] || '';

        // Atualiza os valores dos inputs VISUALMENTE
        tomboInput.value = tomboValueNorm; // Atualiza para a versão normalizada
        descInput.value = newDesc;
        fornInput.value = newForn;

        // --- SIMULA O EVENTO INPUT PARA ATUALIZAR dirtyItems ---
        // Cria eventos de input
        const inputEvent = new Event('input', { bubbles: true, cancelable: true });

        // Dispara o evento para cada campo atualizado
        tomboInput.dispatchEvent(inputEvent);
        descInput.dispatchEvent(inputEvent);
        fornInput.dispatchEvent(inputEvent);
        // --- Fim da simulação ---

        showNotification(`Dados encontrados e aplicados para ${tomboValueNorm}.`, 'success');
        // Talvez desabilitar o botão e o campo tombo após sucesso?
        // tomboInput.readOnly = true;
        // buttonEl.remove(); // Remove o botão

    } else {
        showNotification(`Tombamento ${tomboValueNorm} não encontrado na planilha GIAP.`, 'error');
    }

    // Restaura o botão
    buttonEl.disabled = false;
    buttonEl.innerHTML = `
        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" fill="currentColor" class="pointer-events-none" viewBox="0 0 16 16">
          <path fill-rule="evenodd" d="M8 3a5 5 0 1 0 4.546 2.914.5.5 0 0 1 .908-.417A6 6 0 1 1 8 2z"/>
          <path d="M8 4.466V.534a.25.25 0 0 1 .41-.192l2.36 1.966c.12.1.12.284 0 .384L8.41 4.658A.25.25 0 0 1 8 4.466zM12.5 10a.5.5 0 0 1-.5.5h-4a.5.5 0 0 1 0-1h4a.5.5 0 0 1 .5.5m-5-2.5a.5.5 0 0 1 .5-.5h5a.5.5 0 0 1 0 1h-5a.5.5 0 0 1-.5-.5m-5 5a.5.5 0 0 1 .5-.5h5a.5.5 0 0 1 0 1h-5a.5.5 0 0 1-.5-.5"/>
        </svg>
    `;
}


// --- SALVAR ALTERAÇÕES EM LOTE ---
async function saveAllChanges() {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }

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
                // MUDANÇA: Usa a coleção correta no Firebase
                const docRef = doc(db, getCollectionPath('patrimonio'), itemWithChanges.id);
                // Pega o item ORIGINAL para comparar
                const originalItem = fullInventory.find(i => i.id === itemWithChanges.id);
                if (!originalItem) {
                     console.warn(`Item original ${itemWithChanges.id} não encontrado para salvar.`);
                     return; // Pula este item se o original não existe mais
                }

                // Cria um objeto APENAS com os campos que REALMENTE mudaram
                 const changes = {};
                 let hasChanges = false;
                 Object.keys(itemWithChanges).forEach(key => {
                     if (key !== 'id' && key !== 'createdAt' && key !== 'updatedAt') { // Ignora campos imutáveis
                         // Compara string para robustez
                         const originalValueStr = (originalItem[key] === null || originalItem[key] === undefined) ? '' : String(originalItem[key]);
                         const newValueStr = (itemWithChanges[key] === null || itemWithChanges[key] === undefined) ? '' : String(itemWithChanges[key]);
                         if (originalValueStr !== newValueStr) {
                             changes[key] = itemWithChanges[key]; // Adiciona o valor alterado
                             hasChanges = true;
                         }
                     }
                 });


                // Só atualiza se houver mudanças reais
                if (hasChanges) {
                     console.log(`Updating item ${itemWithChanges.id} with changes:`, changes);
                    chunkBatch.update(docRef, {
                        ...changes,
                        updatedAt: serverTimestamp() // Atualiza timestamp sempre
                    });
                } else {
                     console.log(`Skipping item ${itemWithChanges.id}, no effective changes detected.`);
                }
            });

            await chunkBatch.commit();
            savedCount += chunk.length;
            showOverlay(`Salvando: ${savedCount}/${itemsToSave.length} itens...`);
        }

        // Atualizar cache local e array principal com base nos itens salvos
        await idb.transaction('rw', idb.patrimonio, async () => {
            const itemsToCache = [];
            itemsToSave.forEach(itemWithChanges => {
                const index = fullInventory.findIndex(i => i.id === itemWithChanges.id);
                if (index > -1) {
                     // Mescla as mudanças salvas no item original do inventário
                     // Recria o objeto para garantir que só os campos salvos sejam atualizados
                     const originalItem = fullInventory[index];
                     const finalItemState = { ...originalItem }; // Começa com o original
                     Object.keys(itemWithChanges).forEach(key => {
                         if (key !== 'id' && key !== 'createdAt') { // Ignora imutáveis
                              const originalValueStr = (originalItem[key] === null || originalItem[key] === undefined) ? '' : String(originalItem[key]);
                              const newValueStr = (itemWithChanges[key] === null || itemWithChanges[key] === undefined) ? '' : String(itemWithChanges[key]);
                              if (originalValueStr !== newValueStr) {
                                  finalItemState[key] = itemWithChanges[key]; // Aplica a mudança
                              }
                         }
                     });
                    fullInventory[index] = finalItemState; // Atualiza no array principal
                    itemsToCache.push(fullInventory[index]); // Adiciona item atualizado para cache
                }
            });
            if (itemsToCache.length > 0) {
                await idb.patrimonio.bulkPut(itemsToCache);
                 console.log(`${itemsToCache.length} items updated in cache.`);
            }
        });

        dirtyItems.clear(); // Limpa apenas após sucesso
        hideOverlay();
        showNotification(`✅ ${itemsCount} itens processados e salvos com sucesso!`, 'success');

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
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }

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
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        closeDeleteConfirmModal();
        return;
    }

    if (currentDeleteItemIds.length === 0) return;

    const count = currentDeleteItemIds.length;
    showOverlay(`Excluindo ${count} itens...`);

    try {
        const batch = writeBatch(db);
        currentDeleteItemIds.forEach(id => {
            // MUDANÇA: Usa a coleção correta no Firebase
            batch.delete(doc(db, getCollectionPath('patrimonio'), id));
        });
        await batch.commit();

        // Atualizar localmente
        const idsToDeleteSet = new Set(currentDeleteItemIds);
        fullInventory = fullInventory.filter(item => !idsToDeleteSet.has(item.id));
        await idb.patrimonio.bulkDelete(currentDeleteItemIds);

        // Limpar alterações pendentes dos itens deletados
        currentDeleteItemIds.forEach(id => dirtyItems.delete(id));

         // Recalcula filteredInventory baseado no fullInventory atualizado E re-renderiza
        applyFiltersAndPaginate();

        hideOverlay();
        closeDeleteConfirmModal();
        showNotification(`✅ ${count} itens excluídos!`, 'success');

    } catch (error) {
        hideOverlay();
        showNotification(`❌ Erro ao excluir: ${error.message}`, 'error');
        console.error(error);
    }
}

// --- FIM: SEÇÃO ULTRA OTIMIZADA (Funções coladas) ---

// --- Handlers do Modal Descrição (Definição movida para cá) ---
function handleDescChoiceKeep() {
     addLinkToCreate(false);
    closeDescriptionChoiceModal();
}
function handleDescChoiceUpdate() {
     addLinkToCreate(true);
    closeDescriptionChoiceModal();
}
function handleDescChoiceCancel() {
     selSys = selGiap = null;
    document.querySelectorAll('.reconciliation-list-item.selected').forEach(el => el.classList.remove('selected'));
    closeDescriptionChoiceModal();
}
// --- FIM Handlers Modal Descrição ---

// **NOVA Função:** Salvar Vínculos Pendentes (Conciliação)
async function savePendingLinks(context = 'unidade') {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return false;
    }

    console.log(`Iniciando savePendingLinks para contexto: ${context}`); // LOG ADICIONAL
    if (linksToCreate.length === 0) {
        showNotification('Nenhum vínculo novo para salvar.', 'info');
        return true; // Retorna true pois não há erro
    }

    showOverlay(`Salvando ${linksToCreate.length} vínculos...`);
    const batch = writeBatch(db);
    const itemsToUpdateCache = [];
    const patternsToSave = [];

    linksToCreate.forEach(link => {
        // MUDANÇA: Usa a coleção correta no Firebase
        const systemItemRef = doc(db, getCollectionPath('patrimonio'), link.systemItem.id);
        const finalDesc = link.useGiapDescription
            ? (link.giapItem.Descrição || link.giapItem.Espécie || link.systemItem.Descrição)
            : link.systemItem.Descrição;

        const updatedData = {
            Tombamento: link.giapItem.TOMBAMENTO,
            Descrição: finalDesc,
            Fornecedor: link.giapItem['Nome Fornecedor'] || link.systemItem.Fornecedor || '', // Prioriza GIAP
            NF: link.giapItem.NF || link.systemItem.NF || '', // Prioriza GIAP
            etiquetaPendente: true, // Marca para colocar a etiqueta
            updatedAt: serverTimestamp()
        };

        batch.update(systemItemRef, updatedData);
        // Guarda dados para atualizar cache e array local
        itemsToUpdateLocally.push({ id: link.systemItem.id, changes: updatedData });

        // Prepara padrão de conciliação para salvar
        const score = calculateSimilarity(
            `${link.systemItem.Descrição || ''} ${link.systemItem.Fornecedor || ''}`.trim(),
            `${link.giapItem.Descrição || ''} ${link.giapItem.Espécie || ''} ${link.giapItem['Nome Fornecedor'] || ''}`.trim()
        );
        patternsToSave.push({ systemItem: link.systemItem, giapItem: link.giapItem, score });
    });

    try {
        console.log(`Executando batch com ${linksToCreate.length} updates.`); // LOG ADICIONAL
        await batch.commit();

        // Salva os padrões de conciliação (sem esperar)
        patternsToSave.forEach(p => salvarPadraoConciliacao(p.systemItem, p.giapItem, p.score));

        // Atualiza cache e array principal
        await idb.transaction('rw', idb.patrimonio, async () => {
            for (const itemUpdate of itemsToUpdateCache) {
                 await idb.patrimonio.update(itemUpdate.id, itemUpdate.changes);
                 const index = fullInventory.findIndex(i => i.id === itemUpdate.id);
                 if (index > -1) {
                     // Atualiza o item no array principal
                     fullInventory[index] = { ...fullInventory[index], ...itemUpdate.changes };
                 }
            }
        });
        console.log(`${itemsToUpdateCache.length} itens atualizados localmente.`); // LOG ADICIONAL

        linksToCreate = []; // Limpa a lista de links pendentes APÓS salvar
        renderCreatedLinks(context); // Limpa a UI
        hideOverlay();
        console.log("savePendingLinks concluído com sucesso."); // LOG ADICIONAL
        return true; // Indica sucesso

    } catch (error) {
        hideOverlay();
        showNotification('Erro ao salvar os vínculos.', 'error');
        console.error("Erro ao salvar vínculos:", error);
        return false; // Indica falha
    }
}


// --- SEÇÃO ORIGINAL MANTIDA (Outras Abas) ---
function populateUnitMappingTab() {
    // ... (código original mantido)
    const systemTypes = [...new Set((fullInventory || []).map(i => i.Tipo).filter(Boolean))].sort(); // Fallback
    const mapFilterTipo = document.getElementById('map-filter-tipo');
    if(mapFilterTipo) mapFilterTipo.innerHTML = '<option value="">Todos os Tipos</option>' + systemTypes.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');
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
    let allGiapUnitsFromSheet = [...new Set((giapInventory || []).map(i => i.Unidade).filter(Boolean))]; // Fallback
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
     const pendingTransfers = (fullInventory || []).filter(item => { // Fallback
        if (!item) return false;
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

function parsePtBrDate(dateStr) {
    if (!dateStr || typeof dateStr !== 'string') return new Date(0);
    const parts = dateStr.split('/');
    if (parts.length === 3) {
        // Assume DD/MM/YYYY
        const year = parseInt(parts[2], 10);
        const fullYear = year < 100 ? (year > 50 ? 1900 + year : 2000 + year) : year;
        return new Date(fullYear, parseInt(parts[1], 10) - 1, parseInt(parts[0], 10));
    }
    const isoParts = dateStr.split('-'); // Assume YYYY-MM-DD
    if(isoParts.length === 3) {
        return new Date(parseInt(isoParts[0], 10), parseInt(isoParts[1], 10) - 1, parseInt(isoParts[2], 10));
    }
    const parsedDate = new Date(dateStr);
    return isNaN(parsedDate) ? new Date(0) : parsedDate;
}


function populateNfTab() {
    // ... (código original mantido)
    if (!giapInventory || giapInventory.length === 0) return; // Fallback

    const giapWithNf = giapInventory
        .filter(item => item && item.NF && item.NF.trim() !== '') // Checagem item
        .sort((a, b) => {
            const dateA = parsePtBrDate(a.Cadastro);
            const dateB = parsePtBrDate(b.Cadastro);
            // Ordena decrescente por data (mais recente primeiro)
            return dateB - dateA;
        });


    processedNfData = giapWithNf.reduce((acc, item) => {
        const nf = item.NF.trim();
        if (!acc[nf]) {
            acc[nf] = {
                items: [],
                fornecedor: item['Nome Fornecedor'] || 'Não especificado',
                tipoEntrada: item['Tipo Entrada'] || 'N/A',
                dataCadastro: item.Cadastro
            };
        }
        acc[nf].items.push(item);
        return acc;
    }, {});

    const allStatuses = [...new Set(giapInventory.map(item => item ? (item.Status || '').trim() : '').filter(Boolean))].sort(); // Checagem item
    const statusFilterEl = document.getElementById('nf-status-filter');
    if (statusFilterEl) {
        statusFilterEl.innerHTML = '<option value="">Todos os Status</option>' + allStatuses.map(s => `<option value="${escapeHtml(s)}">${escapeHtml(s)}</option>`).join('');
    }

    renderNfList();
}

// **MODIFICADO:** Função para renderizar lista de NF (Lazy Loading)
function renderNfList() {
    const container = domCache.nfContainer; // Usa cache
    if (!container) return;
    container.innerHTML = ''; // Limpa antes de renderizar
    loadedNfDetails.clear(); // Limpa o set de detalhes carregados

    // Filtros (lógica existente mantida)
    const tomboMap = new Map((fullInventory || []).map(item => item ? [item.Tombamento?.trim(), item] : null).filter(Boolean));
    const nfSearchTerm = document.getElementById('nf-search')?.value.toLowerCase() || '';
    const nfItemSearchTerm = document.getElementById('nf-item-search')?.value.toLowerCase() || '';
    const nfFornecedorTerm = document.getElementById('nf-fornecedor-search')?.value.toLowerCase() || '';
    const nfTipoEntrada = document.getElementById('nf-tipo-entrada')?.value || '';
    const nfStatusFilter = document.getElementById('nf-status-filter')?.value || '';
    const startDateStr = document.getElementById('nf-date-start')?.value || '';
    const endDateStr = document.getElementById('nf-date-end')?.value || '';
    const startDate = startDateStr ? new Date(startDateStr + 'T00:00:00') : null;
    let endDate = endDateStr ? new Date(endDateStr + 'T23:59:59') : null;

    const filteredNfs = Object.keys(processedNfData).filter(nf => {
        const nfGroup = processedNfData[nf];
        if (!nfGroup || !nfGroup.items) return false;
        if (nfSearchTerm && !nf.toLowerCase().includes(nfSearchTerm)) return false;
        if (nfFornecedorTerm && !(nfGroup.fornecedor || '').toLowerCase().includes(nfFornecedorTerm)) return false;
        if (nfItemSearchTerm) {
            if (!nfGroup.items.some(item => (item.Descrição || '').toLowerCase().includes(nfItemSearchTerm) || (item.Espécie || '').toLowerCase().includes(nfItemSearchTerm))) return false;
        }
        if (nfTipoEntrada && (nfGroup.tipoEntrada || '').trim() !== nfTipoEntrada) return false;
        if (nfStatusFilter) {
            if (!nfGroup.items.some(item => (item.Status || '').trim() === nfStatusFilter)) return false;
        }
        const nfDate = parsePtBrDate(nfGroup.dataCadastro);
        if (startDate && nfDate < startDate) return false;
        if (endDate && nfDate > endDate) return false;
        return true;
    });

    filteredNfs.sort((nfA, nfB) => {
         const dateA = parsePtBrDate(processedNfData[nfA].dataCadastro);
         const dateB = parsePtBrDate(processedNfData[nfB].dataCadastro);
         return dateB - dateA;
     });

    if (filteredNfs.length === 0) {
        container.innerHTML = `<p class="text-slate-500 text-center p-4">Nenhuma nota fiscal encontrada com os filtros aplicados.</p>`;
        return;
    }

    const fragment = document.createDocumentFragment(); // Usar fragmento para performance

    const categorizedNfs = filteredNfs.reduce((acc, nfKey) => {
        const nfGroup = processedNfData[nfKey];
        const category = nfGroup.tipoEntrada || 'Outros';
        if (!acc[category]) acc[category] = [];
        acc[category].push(nfKey);
        return acc;
    }, {});

    Object.keys(categorizedNfs).sort().forEach(category => {
        const categoryHeader = document.createElement('h3');
        categoryHeader.className = 'text-lg font-bold text-slate-700 p-2 bg-slate-100 rounded-t-lg mt-6 first:mt-0';
        categoryHeader.textContent = category;
        fragment.appendChild(categoryHeader);

        categorizedNfs[category].forEach(nf => {
            const nfGroup = processedNfData[nf];
            const nfDetails = document.createElement('details');
            nfDetails.className = 'nf-details bg-white rounded-lg shadow-sm border mb-3 border-t-0 rounded-t-none';
            nfDetails.dataset.nfKey = nf; // Guarda a chave NF aqui
            nfDetails.innerHTML = `
                <summary class="nf-summary p-4 font-semibold cursor-pointer grid grid-cols-1 md:grid-cols-3 gap-4 items-center hover:bg-slate-50">
                    <div class="md:col-span-2">
                        <p class="text-xs text-slate-500">NF: <strong class="text-blue-700 text-sm">${escapeHtml(nf)}</strong> | Fornecedor: <strong>${escapeHtml(nfGroup.fornecedor)}</strong></p>
                        <p class="text-xs text-slate-500 mt-1 truncate">Itens: ${escapeHtml(nfGroup.items.slice(0, 2).map(i => i.Descrição || i.Espécie).join(', ')) + (nfGroup.items.length > 2 ? '...' : '')}</p>
                    </div>
                    <div><p class="text-xs text-slate-500">Data Cadastro</p><strong>${escapeHtml(nfGroup.dataCadastro)}</strong></div>
                </summary>
                <div class="nf-items-container p-4 border-t border-slate-200 space-y-2 hidden">
                    <!-- Detalhes serão carregados aqui -->
                    <div class="text-center p-4"><div class="loading-spinner w-8 h-8 mx-auto"></div> Carregando itens...</div>
                </div>
            `;
            fragment.appendChild(nfDetails);
        });
    });

    container.appendChild(fragment); // Adiciona tudo de uma vez
    console.log(`Renderizados ${filteredNfs.length} resumos de NFs.`);
}

// **NOVO:** Handler para carregar detalhes da NF sob demanda
function handleNfDetailsToggle(event) {
    const detailsElement = event.target;

    // Verifica se o evento é no elemento <details> e se está sendo aberto
    if (detailsElement.tagName !== 'DETAILS' || !detailsElement.open) {
        return;
    }

    const nfKey = detailsElement.dataset.nfKey;
    const itemsContainer = detailsElement.querySelector('.nf-items-container');

    // Se já carregou ou não tem a chave, não faz nada
    if (!nfKey || !itemsContainer || loadedNfDetails.has(nfKey)) {
        // Se já carregou, apenas garante que está visível
        if (itemsContainer) itemsContainer.classList.remove('hidden');
        return;
    }

    console.log(`Carregando detalhes para NF: ${nfKey}`);
    itemsContainer.classList.remove('hidden'); // Mostra o container (com o spinner)

    // Simula um pequeno atraso para o spinner aparecer e busca os dados
    setTimeout(() => {
        const nfGroup = processedNfData[nfKey];
        if (!nfGroup || !nfGroup.items) {
            itemsContainer.innerHTML = '<p class="text-red-500">Erro ao carregar itens.</p>';
            return;
        }

        const tomboMap = new Map((fullInventory || []).map(item => item ? [item.Tombamento?.trim(), item] : null).filter(Boolean));
        const nfStatusFilter = document.getElementById('nf-status-filter')?.value || ''; // Pega filtro atual

        let totalNfValue = 0;
        const itemsToDisplay = nfStatusFilter
            ? nfGroup.items.filter(item => (item.Status || '').trim() === nfStatusFilter)
            : nfGroup.items;

        itemsContainer.innerHTML = ''; // Limpa o spinner

        if (itemsToDisplay.length === 0) {
            itemsContainer.innerHTML = '<p class="text-slate-500 text-center p-2">Nenhum item encontrado nesta NF com o filtro de status aplicado.</p>';
        } else {
            itemsToDisplay.forEach(item => {
                totalNfValue += parseCurrency(item['Valor NF']);
                const tombo = item.TOMBAMENTO?.trim();
                const allocatedItem = tombo ? tomboMap.get(tombo) : undefined;
                const status = item.Status || 'N/D';
                const isAvailableForUse = normalizeStr(status).includes(normalizeStr('disponível'));

                let itemClass = allocatedItem ? 'bg-green-50 border-green-200' : (isAvailableForUse ? 'bg-yellow-50 border-yellow-200' : 'bg-slate-100 opacity-60');
                let allocationHtml = allocatedItem
                    ? `<div><p class="px-2 py-1 text-xs font-bold text-green-800 bg-green-200 rounded-full text-center">ENCONTRADO</p><p class="text-xs text-slate-600 mt-1 text-right">→ <strong>${escapeHtml(allocatedItem.Unidade)}</strong></p><p class="text-xs text-slate-500 mt-1 text-right">(${escapeHtml(allocatedItem.Estado)})</p></div>`
                    : `<p class="px-2 py-1 text-xs font-semibold ${isAvailableForUse ? 'text-yellow-800 bg-yellow-100' : 'text-slate-700 bg-slate-200'} rounded-full text-center">NÃO ALOCADO</p>`;
                let statusHtml = `<span class="px-2 py-1 text-xs font-semibold rounded-full ${isAvailableForUse ? 'text-green-800 bg-green-100' : 'text-red-800 bg-red-100'}">${isAvailableForUse ? 'Disponível para uso' : `Indisponível (${escapeHtml(status)})`}</span>`;

                const itemDiv = document.createElement('div');
                itemDiv.className = `p-3 border rounded-md flex justify-between items-start gap-4 ${itemClass}`;
                itemDiv.innerHTML = `
                    <div class="flex-1"><p class="font-bold text-slate-800 ${!allocatedItem && !isAvailableForUse ? 'line-through' : ''}">${escapeHtml(item.Descrição || item.Espécie)}</p><p class="text-sm text-slate-500">Tombamento: <span class="font-mono">${escapeHtml(tombo || 'N/D')}</span></p></div>
                    <div class="text-right"><p class="text-xs text-slate-500">Valor</p><p class="font-semibold text-green-700">${parseCurrency(item['Valor NF']).toLocaleString('pt-BR', { style: 'currency', currency: 'BRL' })}</p></div>
                    <div class="text-right ml-4 space-y-1.5 min-w-[150px]">${statusHtml}${allocationHtml}</div>
                `;
                itemsContainer.appendChild(itemDiv);
            });

            // Mostra o total da NF apenas se todos os itens estiverem sendo exibidos
            if (itemsToDisplay.length === nfGroup.items.length) {
                const totalDiv = document.createElement('div');
                totalDiv.className = 'p-3 border-t-2 mt-2 font-bold text-slate-800 flex justify-between items-center';
                totalDiv.innerHTML = `<span>VALOR TOTAL DA NOTA</span><span>${totalNfValue.toLocaleString('pt-BR', { style: 'currency', currency: 'BRL' })}</span>`;
                itemsContainer.appendChild(totalDiv);
            }
        }


        loadedNfDetails.add(nfKey); // Marca como carregado
    }, 100); // Pequeno delay
}



function populateGiapTab() {
    // ... (código original mantido)
    const giapTableBody = document.getElementById('giap-table-body');
     if (!giapTableBody) return; // Verifica
    const headers = ['TOMBAMENTO', 'Descrição', 'Unidade', 'Status', 'Alocação', 'Cadastro', 'NF', 'Nome Fornecedor'];
    const thead = giapTableBody.closest('table').querySelector('thead tr');
    if (thead) thead.innerHTML = headers.map(h => `<th class="p-3 text-left font-semibold">${h}</th>`).join('');

    const tomboMap = new Map((fullInventory || []).map(item => item ? [normalizeTombo(item.Tombamento), item] : null).filter(Boolean)); // Fallback

    giapTableBody.innerHTML = (giapInventory || []).map(item => { // Fallback
        if (!item) return ''; // Segurança extra
        const tombo = normalizeTombo(item.TOMBAMENTO);
        const allocatedItem = tomboMap.get(tombo);

        let alocacaoHtml = `<span class="px-2 py-1 text-xs font-semibold text-yellow-800 bg-yellow-100 rounded-full">Não Alocado</span>`;
        if (allocatedItem) {
            alocacaoHtml = `<span class="px-2 py-1 text-xs font-semibold text-green-800 bg-green-100 rounded-full">Alocado em: <strong>${escapeHtml(allocatedItem.Unidade)}</strong></span>`;
        }

        const cells = {
            'TOMBAMENTO': escapeHtml(item.TOMBAMENTO),
            'Descrição': escapeHtml(item.Descrição),
            'Unidade': escapeHtml(item.Unidade),
            'Status': escapeHtml(item.Status),
            'Alocação': alocacaoHtml,
            'Cadastro': escapeHtml(item.Cadastro),
            'NF': escapeHtml(item.NF),
            'Nome Fornecedor': escapeHtml(item['Nome Fornecedor'])
        };

        return `<tr class="border-b hover:bg-slate-50">${headers.map(h => `<td class="p-2">${cells[h] || ''}</td>`).join('')}</tr>`;
    }).join('');
}

function populateImportAndReplaceTab() {
    // ... (código original mantido)
    const tipos = [...new Set((fullInventory || []).map(item => item.Tipo).filter(Boolean))].sort(); // Fallback

    const selects = [
        document.getElementById('mass-transfer-tipo'),
        document.getElementById('replace-tipo'),
        document.getElementById('edit-by-desc-tipo')
    ];

    selects.forEach(select => {
        if(select) select.innerHTML = '<option value="">Selecione um Tipo</option>' + tipos.map(t => `<option value="${t}">${t}</option>`).join('');
    });

    const setupUnitSelect = (tipoSelectId, unitSelectId) => {
         const tipoSelect = document.getElementById(tipoSelectId);
         if (!tipoSelect) return; // Adiciona verificação
         tipoSelect.addEventListener('change', () => {
            const selectedTipo = tipoSelect.value;
            const unitSelect = document.getElementById(unitSelectId);
            if (!unitSelect) return; // Adiciona verificação
            if (!selectedTipo) {
                unitSelect.innerHTML = '<option value="">Selecione um Tipo primeiro</option>'; // Mensagem clara
                unitSelect.disabled = true;
                return;
            }
            const unidades = [...new Set((fullInventory || []).filter(i => i.Tipo === selectedTipo).map(i => i.Unidade).filter(Boolean))].sort(); // Fallback
            unitSelect.innerHTML = '<option value="">Selecione uma Unidade</option>' + unidades.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`).join('');
            unitSelect.disabled = false;
        });
        // Garante que o select de unidade comece desabilitado
        const unitSelectInitial = document.getElementById(unitSelectId);
         if(unitSelectInitial) {
             unitSelectInitial.innerHTML = '<option value="">Selecione um Tipo primeiro</option>';
             unitSelectInitial.disabled = true;
         }
    };

    setupUnitSelect('mass-transfer-tipo', 'mass-transfer-unit');
    setupUnitSelect('replace-tipo', 'replace-unit');
    setupUnitSelect('edit-by-desc-tipo', 'edit-by-desc-unit');
}

function populateReconciliationTab() {
    // ... (código original mantido)
    const tipos = [...new Set((fullInventory || []).map(item => item.Tipo).filter(Boolean))].sort(); // Fallback
    const sel = document.getElementById('filter-tipo');
    if (sel) sel.innerHTML = '<option value="">Todos os Tipos</option>' + tipos.map(t => `<option value="${t}">${t}</option>`).join('');

    const tombarFilterTipo = document.getElementById('tombar-filter-tipo');
     if (tombarFilterTipo) tombarFilterTipo.innerHTML = '<option value="">Todos os Tipos</option>' + tipos.map(t => `<option value="${t}">${t}</option>`).join('');

    // Garante que o select de unidade comece desabilitado
    const selU = document.getElementById('filter-unidade');
    if (selU) {
        selU.innerHTML = '<option value="">Selecione um Tipo primeiro</option>';
        selU.disabled = true;
    }
    const selUTombar = document.getElementById('tombar-filter-unidade');
    if (selUTombar) {
        selUTombar.innerHTML = '<option value="">Selecione um Tipo primeiro</option>';
        selUTombar.disabled = true;
    }
}


function renderList(containerId, arr, keyField, primaryLabelField, suggestionInfo = null, context = 'default') {
    // ... (código original mantido)
    const container = document.getElementById(containerId);
    if (!container) return; // Adiciona verificação
    container.innerHTML = '';
    if (!arr || arr.length === 0) {
        container.innerHTML = `<p class="p-4 text-slate-500 text-center">Nenhum item encontrado.</p>`;
        return;
    }
    arr.forEach((item, index) => {
        if (!item) return; // Segurança extra
        const id = item[keyField];
         if (id === undefined || id === null) {
             console.warn("Item skipped in renderList due to missing keyField:", item);
             return; // Pula itens sem ID/Tombo
         }
        const div = document.createElement('div');
        div.className = 'reconciliation-list-item card p-2 text-sm';
        div.dataset.id = id;

        let detailsHtml = '';
        if (containerId.includes('system-list')) { // Itens S/T do Sistema
             detailsHtml = `
                <strong>${escapeHtml(item[primaryLabelField] || 'Sem Descrição')}</strong>
                <p class="text-xs text-slate-500 mt-1">Fornecedor: ${escapeHtml(item.Fornecedor || 'N/D')} | Estado: <strong>${escapeHtml(item.Estado || 'N/A')}</strong></p>
                <p class="text-xs text-slate-400 mt-1">Obs: ${escapeHtml(item.Observação || 'Nenhuma')}</p>
            `;
        } else { // Itens Tombados (GIAP)
             const valorNFFormatado = parseCurrency(item['Valor NF']).toLocaleString('pt-BR', { style: 'currency', currency: 'BRL' });
             detailsHtml = `
                <div class="flex justify-between items-start">
                    <div class="flex-1">
                        <strong>${escapeHtml(item[keyField])} - ${escapeHtml(item.Descrição || item.Espécie || 'N/A')}</strong>
                        <p class="text-xs text-slate-500 mt-1">Cadastro: <strong>${escapeHtml(item.Cadastro || 'N/D')}</strong> | NF: <strong>${escapeHtml(item['NF'] || 'N/A')}</strong></p>
                        <p class="text-xs text-slate-500 mt-1">Fornecedor: <strong>${escapeHtml(item['Nome Fornecedor'] || 'N/D')}</strong></p>
                    </div>
                    <div class="text-right ml-2"><p class="text-xs text-slate-500">Valor NF</p><strong class="text-sm text-green-700">${valorNFFormatado}</strong></div>
                </div>`;
            if (context === 'sobras') {
                 detailsHtml += `<p class="text-xs text-blue-600 font-semibold mt-1">Unidade GIAP Original: ${escapeHtml(item.Unidade || 'N/A')}</p>`;
            }
        }

        div.innerHTML = detailsHtml;

        // Aplica estilo de sugestão
        if (suggestionInfo && suggestionInfo.suggestions.has(id)) {
            const score = suggestionInfo.suggestions.get(id);
             // Destaca a melhor sugestão com score alto, outras sugestões boas com cor diferente
             if (index === 0 && score >= 0.75) {
                 div.style.backgroundColor = '#dbeafe'; // Azul claro forte
                 div.style.borderLeft = '4px solid #2563eb'; // Azul forte
             } else if (score >= 0.60) { // Limiar mais baixo para sugestões secundárias
                 div.style.backgroundColor = '#e0f2fe'; // Azul claro mais suave
                 div.style.borderLeft = '4px solid #7dd3fc'; // Azul mais suave
             }
        }

        div.onclick = (event) => handleSelect(containerId, id, item, event.currentTarget);
        container.append(div);
    });
}

function getGlobalLeftovers() {
    // ... (código original mantido)
    const usedTombamentos = new Set((fullInventory || []).map(i => i ? normalizeTombo(i.Tombamento) : null).filter(Boolean)); // Fallback
    linksToCreate.forEach(link => usedTombamentos.add(normalizeTombo(link.giapItem.TOMBAMENTO)));

    return (giapInventory || []).filter(g => { // Fallback
        if (!g) return false; // Segurança extra
        const tombo = normalizeTombo(g.TOMBAMENTO);
        // Garante que o status 'Disponível' seja verificado corretamente
        const statusOK = g.Status && normalizeStr(g.Status).includes(normalizeStr('Disponível'));
        return tombo && !tombo.includes('permuta') && !usedTombamentos.has(tombo) && statusOK;
    });
}


function getConciliationData() {
    // ... (código original mantido)
    const unidade = document.getElementById('filter-unidade').value.trim();
    if (!unidade) return { systemItems: [], giapItems: [] };

    const systemFilterText = normalizeStr(document.getElementById('system-list-filter').value);
    const giapFilterText = normalizeStr(document.getElementById('giap-list-filter').value);

    const usedTombamentos = new Set((fullInventory || []).map(i => i ? normalizeTombo(i.Tombamento) : null).filter(Boolean)); // Fallback
    linksToCreate.forEach(link => usedTombamentos.add(normalizeTombo(link.giapItem.TOMBAMENTO)));

    const mappedGiapUnits = unitMapping[unidade] || [unidade];
    const mappedGiapUnitsNormalized = mappedGiapUnits.map(normalizeStr); // Normaliza unidades mapeadas

    const systemItems = (fullInventory || []).filter(i => { // Fallback
        if (!i) return false;
        const tombo = (i.Tombamento || '').trim().toLowerCase();
        const isPending = linksToCreate.some(l => l.systemItem.id === i.id);
        return !isPending &&
               !i.isPermuta && // <-- EXCLUI PERMUTA
               i.Unidade === unidade &&
               (tombo === '' || tombo === 's/t') &&
               normalizeStr(i.Descrição || '').includes(systemFilterText); // Adiciona fallback para Descrição
    });

    const giapItems = (giapInventory || []).filter(g => { // Fallback
        if (!g) return false;
        const tomboTrimmed = normalizeTombo(g.TOMBAMENTO);
        const giapDesc = normalizeStr(g.Descrição || g.Espécie || ''); // Adiciona fallback
         const statusOK = g.Status && normalizeStr(g.Status).includes(normalizeStr('Disponível')); // Verifica status
         const unitMatch = g.Unidade && mappedGiapUnitsNormalized.includes(normalizeStr(g.Unidade)); // Compara unidades normalizadas
        return tomboTrimmed &&
               !usedTombamentos.has(tomboTrimmed) &&
               unitMatch && // Verifica correspondência de unidade
               statusOK && // Verifica status
               giapDesc.includes(giapFilterText);
    });

    return { systemItems, giapItems };
}


function handleSelect(containerId, id, obj, element) {
    // ... (código original mantido)
    if (element.classList.contains('linked')) return;

    const activeTabEl = document.querySelector('#content-conciliar .sub-nav-btn.active');
    const activeSubTab = activeTabEl ? activeTabEl.dataset.subtabConciliar : 'conciliacao_unidade';
    const isSobrantesTab = activeSubTab === 'conciliacao_sobras';

    const systemListSelector = isSobrantesTab ? '#sobras-system-list' : '#system-list';
    const giapListSelector = isSobrantesTab ? '#sobras-giap-list' : '#giap-list';


    if (containerId.includes('system-list')) { // Se clicou na lista do Sistema (S/T)
        // MUDANÇA: Bloqueia a ação se for anônimo
         if (auth.currentUser?.isAnonymous) {
             showNotification('Acesso negado. Ações de conciliação são apenas para usuários autenticados.', 'error');
             return;
         }

        clearGiapImportSelection(); // Limpa seleção de importação (se houver)
        selSys = { id, obj };
        selGiap = null; // Reseta seleção GIAP

        // Limpa seleção visual em ambas as listas GIAP e marca o item clicado
        document.querySelectorAll(`${giapListSelector} .selected, ${giapListSelector} .selected-for-import`).forEach(el => el.classList.remove('selected', 'selected-for-import'));
        document.querySelectorAll(`${systemListSelector} .selected`).forEach(el => el.classList.remove('selected'));
        element.classList.add('selected');

        // Busca sugestões na lista GIAP correspondente
        const giapSourceItems = isSobrantesTab ? getFilteredSobrantes() : getConciliationData().giapItems;
        suggestGiapMatchesComAprendizado(obj, giapSourceItems);

    } else if (containerId.includes('giap-list') && selSys) { // Se clicou na lista GIAP e JÁ TEM um item do sistema selecionado
        selGiap = { tomb: id, obj }; // Define o item GIAP selecionado
        // Limpa seleção visual na lista GIAP e marca o item clicado
        document.querySelectorAll(`${giapListSelector} .selected, ${giapListSelector} .selected-for-import`).forEach(el => el.classList.remove('selected', 'selected-for-import'));
        element.classList.add('selected');
        openDescriptionChoiceModal(); // Abre o modal para escolher a descrição

    } else if (containerId.includes('giap-list') && !selSys && !isSobrantesTab) { // Se clicou na lista GIAP SEM item do sistema selecionado (e não está na aba Sobras) -> MODO IMPORTAÇÃO
         // MUDANÇA: Bloqueia a ação se for anônimo
         if (auth.currentUser?.isAnonymous) {
             showNotification('Acesso negado. Ações de importação são apenas para usuários autenticados.', 'error');
             return;
         }

        element.classList.toggle('selected-for-import'); // Alterna a classe de seleção para importação
        const index = giapItemsForImport.findIndex(item => item.TOMBAMENTO === id);
        if (index > -1) {
            giapItemsForImport.splice(index, 1); // Remove se já estava selecionado
        } else {
            giapItemsForImport.push(obj); // Adiciona se não estava
        }
        updateImportButton(); // Atualiza o botão de importação
    } else if (containerId.includes('giap-list') && !selSys && isSobrantesTab) {
         // Na aba Sobras, clicar num item GIAP sem item de sistema selecionado não faz nada (ou poderia mostrar detalhes?)
         console.log("Selecionado item GIAP sobrando:", obj);
         // Limpa seleção visual e marca o clicado (apenas visual)
         document.querySelectorAll(`${giapListSelector} .selected, ${giapListSelector} .selected-for-import`).forEach(el => el.classList.remove('selected', 'selected-for-import'));
         element.classList.add('selected');
         selGiap = { tomb: id, obj }; // Guarda a seleção caso o próximo clique seja no sistema
    } else if (containerId.includes('system-list') && selGiap && isSobrantesTab) {
         // MUDANÇA: Bloqueia a ação se for anônimo
         if (auth.currentUser?.isAnonymous) {
             showNotification('Acesso negado. Ações de conciliação são apenas para usuários autenticados.', 'error');
             return;
         }
         // Clicou num item do sistema DEPOIS de clicar num GIAP sobrando
         selSys = { id, obj };
         document.querySelectorAll(`${systemListSelector} .selected`).forEach(el => el.classList.remove('selected'));
         element.classList.add('selected');
         openDescriptionChoiceModal(); // Abre o modal para confirmar o vínculo
    }
}


function updateImportButton() {
    // ... (código original mantido)
    const count = giapItemsForImport.length;
    const btn = document.getElementById('import-giap-btn');
    const countEl = document.getElementById('giap-import-count');
    if(countEl) countEl.textContent = count;
    if(btn) btn.disabled = count === 0 || auth.currentUser?.isAnonymous; // MUDANÇA: Desabilita se for anônimo
}

function clearGiapImportSelection() {
    // ... (código original mantido)
    giapItemsForImport = [];
    document.querySelectorAll('#giap-list .selected-for-import').forEach(el => el.classList.remove('selected-for-import'));
    updateImportButton();
}

function addLinkToCreate(useGiapDescription) {
    // ... (código original mantido)
    if (!selSys || !selGiap) {
         console.error("Tentativa de criar link sem seleção completa.");
         showNotification("Erro: Selecione um item de cada lista.", "error");
         return;
    }
    const link = {
        systemItem: selSys.obj,
        giapItem: selGiap.obj,
        useGiapDescription
    };
    linksToCreate.push(link);

    const activeTabEl = document.querySelector('#content-conciliar .sub-nav-btn.active');
    const activeSubTab = activeTabEl ? activeTabEl.dataset.subtabConciliar : 'conciliacao_unidade';
    const isSobrantesTab = activeSubTab === 'conciliacao_sobras';

    const systemListSelector = isSobrantesTab ? '#sobras-system-list' : '#system-list';
    const giapListSelector = isSobrantesTab ? '#sobras-giap-list' : '#giap-list';


    if(isSobrantesTab) {
        renderCreatedLinks('sobras');
        const systemEl = document.querySelector(`${systemListSelector} div[data-id='${selSys.id}']`);
        if (systemEl) systemEl.classList.add('linked');
        const giapEl = document.querySelector(`${giapListSelector} div[data-id='${selGiap.tomb}']`);
        if (giapEl) giapEl.classList.add('linked');
    } else {
         renderCreatedLinks('unidade');
        const systemEl = document.querySelector(`${systemListSelector} div[data-id='${selSys.id}']`);
        if (systemEl) systemEl.classList.add('linked');
        const giapEl = document.querySelector(`${giapListSelector} div[data-id='${selGiap.tomb}']`);
        if (giapEl) giapEl.classList.add('linked');
    }

    selSys = selGiap = null; // Limpa seleções após criar o link
    document.querySelectorAll('.reconciliation-list-item.selected').forEach(el => el.classList.remove('selected'));
}


function renderCreatedLinks(context = 'unidade') {
    // ... (código original mantido)
    const containerId = context === 'unidade' ? 'created-links' : 'sobras-created-links';
    const container = document.getElementById(containerId);
     if (!container) return; // Adiciona verificação
    container.innerHTML = linksToCreate.map((link, index) => {
        const systemDesc = link.systemItem.Descrição;
        const giapDesc = link.giapItem.Descrição || link.giapItem.Espécie;
        const finalDesc = link.useGiapDescription ? giapDesc : systemDesc;

        return `<div class="created-link-item card link-success p-2 text-sm bg-green-50 border-l-4 border-green-500">
                    <span>
                        <strong>S/T:</strong> ${escapeHtml(systemDesc)} ↔
                        <strong>Tombo:</strong> ${escapeHtml(link.giapItem.TOMBAMENTO)}<br>
                        <span class="text-xs text-blue-700">Descrição a ser salva: "${escapeHtml(finalDesc)}"</span>
                    </span>
                    <button class="delete-link-btn" data-index="${index}" title="Remover Vínculo">
                        <svg class="pointer-events-none" xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" viewBox="0 0 16 16">
                            <path d="M5.5 5.5A.5.5 0 0 1 6 6v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m2.5 0a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m3 .5a.5.5 0 0 0-1 0v6a.5.5 0 0 0 1 0V6z"/>
                            <path fill-rule="evenodd" d="M14.5 3a1 1 0 0 1-1 1H13v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V4h-.5a1 1 0 0 1-1-1V2a1 1 0 0 1 1-1H6a1 1 0 0 1 1-1h2a1 1 0 0 1 1 1h3.5a1 1 0 0 1 1 1v1zM4.118 4 4 4.059V13a1 1 0 0 0 1 1h6a1 1 0 0 0 1-1V4.059L11.882 4H4.118zM2.5 3h11V2h-11v1z"/>
                        </svg>
                    </button>
                </div>`;
    }).join('');
}

function renderConciliationLists() {
    // ... (código original mantido)
    const unidade = document.getElementById('filter-unidade').value.trim();
    if (!unidade) {
        document.getElementById('system-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione uma unidade e clique em carregar.</p>`;
        document.getElementById('giap-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione uma unidade e clique em carregar.</p>`;
        return;
    }

    const { systemItems, giapItems } = getConciliationData();

    renderList('system-list', systemItems, 'id', 'Descrição');
    renderList('giap-list', giapItems, 'TOMBAMENTO', 'Descrição');
}

function openDescriptionChoiceModal() {
    // ... (código original mantido)
    if (!selSys || !selGiap) return;
    const descChoiceModal = document.getElementById('desc-choice-modal');
    if (!descChoiceModal) return; // Verifica
    document.getElementById('desc-choice-tombo').textContent = selGiap.tomb;
    document.getElementById('desc-choice-current').textContent = selSys.obj.Descrição;
    document.getElementById('desc-choice-new').textContent = selGiap.obj.Descrição || selGiap.obj.Espécie;

    descChoiceModal.classList.remove('hidden');
}

function closeDescriptionChoiceModal() {
    // ... (código original mantido)
     const descChoiceModal = document.getElementById('desc-choice-modal');
    if (descChoiceModal) descChoiceModal.classList.add('hidden');
}


function renderItensATombar() {
    // ... (código original mantido)
    const container = document.getElementById('itens-a-tombar-container');
    if (!container) return; // Verifica
    const tipo = document.getElementById('tombar-filter-tipo').value;
    const unidade = document.getElementById('tombar-filter-unidade').value;

    const itemsPendentes = (fullInventory || []).filter(item => // Fallback
        item && item.etiquetaPendente === true && // Checagem item
        (!tipo || item.Tipo === tipo) &&
        (!unidade || item.Unidade === unidade)
    );

    if (itemsPendentes.length === 0) {
        container.innerHTML = '<p class="text-slate-500 text-center p-4">Nenhum item pendente de tombamento com os filtros selecionados.</p>';
        return;
    }

    const groupedByTipo = itemsPendentes.reduce((acc, item) => {
        const tipoKey = item.Tipo || 'Sem Tipo';
        if (!acc[tipoKey]) acc[tipoKey] = {};
        acc[tipoKey].push(item);
        return acc;
    }, {});

    let html = '';
    // MUDANÇA: Verifica se é Admin (não anônimo) para mostrar o botão de confirmação
    const isAnonymous = auth.currentUser?.isAnonymous;
    const actionButton = isAnonymous ? '' : `<button data-id="${item.id}" class="confirmar-tombamento-btn text-xs bg-green-100 text-green-700 px-3 py-1 rounded-md hover:bg-green-200">Confirmar Tombamento</button>`;


    for (const tipo of Object.keys(groupedByTipo).sort()) {
        html += `<h3 class="text-lg font-bold text-slate-700 p-2 bg-slate-100 rounded-t-lg mt-4">${tipo}</h3>`;

        const groupedByUnidade = groupedByTipo[tipo].reduce((acc, item) => {
            const unidadeKey = item.Unidade || 'Sem Unidade';
            if (!acc[unidadeKey]) acc[unidadeKey] = [];
            acc[unidadeKey].push(item);
            return acc;
        }, {});

        for (const unidade of Object.keys(groupedByUnidade).sort()) {
            html += `<details class="bg-white rounded-lg shadow-sm border mb-2" open><summary class="p-4 font-semibold cursor-pointer hover:bg-slate-50">${unidade}</summary>
                        <div class="p-2 border-t">
                            <table class="w-full text-sm">
                                <thead><tr class="border-b"><th class="p-2 text-left">Descrição</th><th class="p-2 text-left">Novo Tombo</th><th class="p-2 text-left">${isAnonymous ? 'Status' : 'Ação'}</th></tr></thead>
                                <tbody>`;

            groupedByUnidade[unidade].forEach(item => {
                html += `<tr class="border-b hover:bg-green-50">
                            <td class="p-2">${escapeHtml(item.Descrição)}</td>
                            <td class="p-2 font-mono">${escapeHtml(item.Tombamento)}</td>
                            <td class="p-2">
                                ${isAnonymous ? '<span class="text-xs text-slate-500">Pendente</span>' : `<button data-id="${item.id}" class="confirmar-tombamento-btn text-xs bg-green-100 text-green-700 px-3 py-1 rounded-md hover:bg-green-200">Confirmar Tombamento</button>`}
                            </td>
                        </tr>`;
            });

            html += `</tbody></table></div></details>`;
        }
    }
    container.innerHTML = html;
}

function populateSobrantesTab() {
     // ... (código original mantido)
    const reconciledTypes = [...new Set((fullInventory || []).filter(i => i && reconciledUnits.includes(i.Unidade)).map(i => i.Tipo).filter(Boolean))].sort(); // Fallback e checagem item
    const sobrasTipoSelect = document.getElementById('sobras-filter-tipo');
    if (sobrasTipoSelect) sobrasTipoSelect.innerHTML = '<option value="">Selecione um Tipo</option>' + reconciledTypes.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');

    const sobrasGiapTypeSelect = document.getElementById('sobras-giap-type-filter');
    const allTypes = [...new Set((fullInventory || []).map(i => i.Tipo).filter(Boolean))].sort(); // Fallback
    if(sobrasGiapTypeSelect) sobrasGiapTypeSelect.innerHTML = '<option value="">Todos os Tipos</option>' + allTypes.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');

    if (sobrasTipoSelect) {
        sobrasTipoSelect.onchange = () => {
            const selectedTipo = sobrasTipoSelect.value;
            const sobrasUnidadeSelect = document.getElementById('sobras-filter-unidade');

            const unitsToShow = reconciledUnits.filter(unitName => {
                if (!selectedTipo) return true;
                const item = fullInventory.find(i => i.Unidade === unitName);
                return item && item.Tipo === selectedTipo;
            }).sort();

            sobrasUnidadeSelect.innerHTML = '<option value="">Selecione uma Unidade</option>' + unitsToShow.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`).join('');
            sobrasUnidadeSelect.disabled = !selectedTipo;
        };
    }

     // Garante que o select de unidade comece desabilitado
    const sobrasUnidadeSelectInitial = document.getElementById('sobras-filter-unidade');
    if (sobrasUnidadeSelectInitial) {
        sobrasUnidadeSelectInitial.innerHTML = '<option value="">Selecione um Tipo primeiro</option>';
        sobrasUnidadeSelectInitial.disabled = true;
    }

    const sysList = document.getElementById('sobras-system-list');
    if(sysList) sysList.innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione Tipo e Unidade e clique em Carregar.</p>`;
    const giapList = document.getElementById('sobras-giap-list');
    if(giapList) giapList.innerHTML = `<p class="p-4 text-slate-500 text-center">Os tombos sobrando aparecerão aqui após carregar os itens do sistema.</p>`;
}

function getFilteredSobrantes() {
     // ... (código original mantido)
    let allLeftovers = getGlobalLeftovers();
    const giapTypeFilterEl = document.getElementById('sobras-giap-type-filter');
    const giapDescFilterEl = document.getElementById('sobras-giap-list-filter');
    const giapTypeFilter = giapTypeFilterEl ? giapTypeFilterEl.value : '';
    const giapDescFilter = giapDescFilterEl ? normalizeStr(giapDescFilterEl.value) : '';

    const giapUnitToSystemType = {};
    Object.keys(unitMapping).forEach(systemUnit => {
        const systemUnitType = (fullInventory.find(i => i.Unidade === systemUnit) || {}).Tipo;
        if(systemUnitType){
            unitMapping[systemUnit].forEach(giapUnit => { giapUnitToSystemType[giapUnit] = systemUnitType; });
        }
    });

    if (giapTypeFilter) {
        allLeftovers = allLeftovers.filter(item => (giapUnitToSystemType[item.Unidade] || 'Não Mapeado') === giapTypeFilter);
    }

    if (giapDescFilter) {
        allLeftovers = allLeftovers.filter(item => normalizeStr(item.Descrição || item.Espécie).includes(giapDescFilter));
    }
    return allLeftovers;
}

function renderSobrantesConciliation() {
     // MUDANÇA: Bloqueia a ação se for anônimo
     if (auth.currentUser?.isAnonymous) {
         showNotification('Acesso negado. Ações de conciliação são apenas para usuários autenticados.', 'error');
         return;
     }

    const unidade = document.getElementById('sobras-filter-unidade').value;
    if (!unidade) {
        showNotification('Selecione uma unidade para carregar os itens S/T.', 'warning');
        return;
    }
    linksToCreate = [];
    renderCreatedLinks('sobras');

    const systemFilterText = normalizeStr(document.getElementById('sobras-system-list-filter').value);
    const systemItems = (fullInventory || []).filter(i => { // Fallback
        if (!i) return false;
        const tombo = (i.Tombamento || '').trim().toLowerCase();
        const isPending = linksToCreate.some(l => l.systemItem.id === i.id);
        return !isPending &&
               !i.isPermuta &&
               i.Unidade === unidade &&
               (tombo === '' || tombo === 's/t') &&
               normalizeStr(i.Descrição || '').includes(systemFilterText); // Fallback
    });

    renderList('sobras-system-list', systemItems, 'id', 'Descrição', null, 'sobras');
    const quickActions = document.getElementById('sobras-quick-actions');
    if (quickActions) quickActions.classList.remove('hidden');


    const filteredSobrantes = getFilteredSobrantes();
    renderList('sobras-giap-list', filteredSobrantes, 'TOMBAMENTO', 'Descrição', null, 'sobras');
}

// findBestMatchForItem, renderEditByDescPreview já estão definidas

// --- FIM: SEÇÃO ORIGINAL MANTIDA ---


// --- HANDLERS DE EVENTOS (Separados para organização) ---

// Handlers da Aba Otimizada (já existem na seção otimizada)
// - applyFiltersAndPaginate, saveAllChanges, goToPage, confirmDeleteItems

// Handlers da Aba Ligar Unidades
async function handleSaveMapping() {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }

    const mapSystemUnitSelect = document.getElementById('map-system-unit-select');
    const mapGiapUnitMultiselect = document.getElementById('map-giap-unit-multiselect');
    if (!mapSystemUnitSelect || !mapGiapUnitMultiselect) return; // Verifica

    const systemUnits = Array.from(mapSystemUnitSelect.selectedOptions).map(opt => opt.value.trim());
    if (systemUnits.length === 0) return showNotification("Selecione uma ou mais Unidades do Sistema.", "warning");
    const giapUnits = Array.from(mapGiapUnitMultiselect.selectedOptions).map(opt => opt.value);
    systemUnits.forEach(systemUnit => { unitMapping[systemUnit] = giapUnits; });
    try {
        if(domCache.feedbackStatus) domCache.feedbackStatus.innerHTML = `<div class="saving-spinner inline-block mr-2"></div> Salvando...`;
        // MUDANÇA: Usa a coleção correta no Firebase
        await setDoc(doc(db, getCollectionPath('config'), 'unitMapping'), { mappings: unitMapping });
        showNotification('Mapeamento salvo!', 'success');
        if(domCache.feedbackStatus) domCache.feedbackStatus.textContent = `Mapeamento salvo!`;
        populateUnitMappingTab(); // Re-renderiza a lista de mapeamentos salvos
    } catch (error) { showNotification(`Erro ao salvar.`, 'error'); console.error(error); if(domCache.feedbackStatus) domCache.feedbackStatus.textContent = `Erro ao salvar.`; }
}

async function handleDeleteMapping(e) {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }
    const deleteBtn = e.target.closest('.delete-mapping-btn');
    if (deleteBtn) {
        const systemUnit = (deleteBtn.dataset.systemUnit || '').trim();
        delete unitMapping[systemUnit];
        try {
            if(domCache.feedbackStatus) domCache.feedbackStatus.innerHTML = `<div class="saving-spinner inline-block mr-2"></div> Removendo...`;
            // MUDANÇA: Usa a coleção correta no Firebase
            await setDoc(doc(db, getCollectionPath('config'), 'unitMapping'), { mappings: unitMapping });
            showNotification(`Ligação removida.`, 'success');
            if(domCache.feedbackStatus) domCache.feedbackStatus.textContent = `Ligação removida.`;
            populateUnitMappingTab(); // Re-renderiza a lista
        } catch (error) { showNotification(`Erro ao remover.`, 'error'); console.error(error); if(domCache.feedbackStatus) domCache.feedbackStatus.textContent = `Erro ao remover.`; }
    }
}

// Handlers da Aba Conciliar
function handleConciliationTypeChange() {
    const filterTipo = document.getElementById('filter-tipo');
    const filterUnidade = document.getElementById('filter-unidade');
    if (!filterTipo || !filterUnidade) return; // Verifica

    const tipo = filterTipo.value;
    const unidades = [...new Set((fullInventory || []) // Fallback
        .filter(i => i && !reconciledUnits.includes(i.Unidade)) // Checagem item
        .filter(i => !tipo || i.Tipo === tipo)
        .map(i => i.Unidade).filter(Boolean))].sort();

    filterUnidade.innerHTML = '<option value="">Selecione uma Unidade</option>' + unidades.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`).join('');
    filterUnidade.disabled = !tipo && unidades.length === 0; // Habilita se tipo for selecionado ou se houver unidades mesmo sem tipo
}


function handleLoadConciliation() {
    const unidadeEl = document.getElementById('filter-unidade');
    const tipoEl = document.getElementById('filter-tipo');
    const warningDiv = document.getElementById('unit-reconciled-warning');
    if(!unidadeEl || !tipoEl || !warningDiv) return; // Verifica

    const unidade = unidadeEl.value.trim();
    const tipo = tipoEl.value;


    if (!unidade) {
        warningDiv.classList.add('hidden');
        return showNotification('Por favor, selecione uma unidade para carregar.', 'warning');
    }

    if(reconciledUnits.includes(unidade)) {
        warningDiv.textContent = `Aviso: Esta unidade já foi finalizada. Para continuar a conciliá-la, vá para a aba "Conciliar com Sobras".`;
        warningDiv.classList.remove('hidden');
    } else {
        warningDiv.classList.add('hidden');
    }

    activeConciliationUnit = unidade;
    activeConciliationType = tipo;

    const unitNameEl = document.getElementById('giap-list-unit-name');
    if(unitNameEl) unitNameEl.textContent = unidade;
    const mappedGiapUnits = unitMapping[unidade] || [unidade];
    // Verifica se existe mapeamento E se ele é diferente da própria unidade (senão, não foi mapeado)
    const isMapped = unitMapping.hasOwnProperty(unidade) && (mappedGiapUnits.length > 1 || mappedGiapUnits[0] !== unidade);
    if(!isMapped && mappedGiapUnits[0] === unidade) { // Só mostra aviso se realmente não foi mapeado
        showNotification('Esta unidade não está mapeada explicitamente. Vá para a aba "Ligar Unidades" para garantir a correspondência correta.', 'warning', 6000);
    }


    document.getElementById('system-list-filter').value = '';
    document.getElementById('giap-list-filter').value = '';
    linksToCreate = [];
    renderCreatedLinks('unidade');
    renderConciliationLists();
    clearGiapImportSelection();

    document.getElementById('quick-actions')?.classList.remove('hidden');
    selSys = selGiap = null;
}

function handleClearConciliationSelections() {
    selSys = selGiap = null;
    document.querySelectorAll('#system-list .selected').forEach(el => el.classList.remove('selected'));
    // Também limpa seleções na lista GIAP
    document.querySelectorAll('#giap-list .selected, #giap-list .selected-for-import').forEach(el => el.classList.remove('selected', 'selected-for-import'));
    clearGiapImportSelection(); // Limpa a contagem de importação
    showNotification('Seleções limpas.', 'info');
    // Talvez re-renderizar a lista GIAP sem sugestões
    if(document.getElementById('filter-unidade')?.value) {
         const { giapItems } = getConciliationData();
         renderList('giap-list', giapItems, 'TOMBAMENTO', 'Descrição');
    }
}

function handleSaveLinksResult(success) {
    if (success) {
        showNotification('Vínculos salvos! Atualizando listas...', 'success');
        renderConciliationLists();
        // Não esconde o overlay aqui, pois pode ser chamado pelo finish
    } else {
        hideOverlay(); // Esconde o overlay se deu erro
    }
}
function handleSaveLinksResultSobras(success) { // Handler separado para Sobras
    if (success) {
        showNotification('Vínculos salvos! Atualizando listas...', 'success');
        renderSobrantesConciliation();
        hideOverlay();
    } else {
         hideOverlay(); // Esconde o overlay se deu erro
    }
}


async function handleFinishReconciliation() {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }

    const unidadeEl = document.getElementById('filter-unidade');
    if (!unidadeEl) return; // Verifica
    const unidade = unidadeEl.value.trim();
    const success = await savePendingLinks('unidade'); // Salva pendências antes de mudar
    if (success) {
        showOverlay('Finalizando unidade...');
        if (unidade && !reconciledUnits.includes(unidade)) {
            reconciledUnits.push(unidade);
            try {
                // MUDANÇA: Usa a coleção correta no Firebase
                await setDoc(doc(db, getCollectionPath('config'), 'reconciledUnits'), { units: reconciledUnits });
                showNotification(`Unidade "${unidade}" movida para a conciliação de sobras.`, 'info');
                // Atualiza o select de unidades na aba principal de conciliação
                 handleConciliationTypeChange();
            } catch (error) {
                hideOverlay();
                showNotification('Erro ao salvar o estado da unidade.', 'error');
                console.error(error);
                return;
            }
        }

        // Muda para a sub-aba de sobras
        const subTab = 'conciliacao_sobras';
        document.querySelectorAll('#content-conciliar .sub-nav-btn').forEach(btn => btn.classList.toggle('active', btn.dataset.subtabConciliar === subTab));
        document.getElementById('subtab-conciliar-unidade').classList.add('hidden');
        document.getElementById('subtab-conciliar-sobras').classList.remove('hidden');
        document.getElementById('subtab-conciliar-itens_a_tombar').classList.add('hidden');

        // Popula a aba de sobras
        if (!initializedTabs.has(subTab)) { // Inicializa se for a primeira vez
            populateSobrantesTab();
             initializedTabs.add(subTab);
        } else {
             populateSobrantesTab(); // Apenas repopula os filtros
        }
        // Limpa as listas ao mudar
        document.getElementById('sobras-system-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione Tipo e Unidade e clique em Carregar.</p>`;
        document.getElementById('sobras-giap-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Os tombos sobrando aparecerão aqui.</p>`;
        document.getElementById('sobras-created-links').innerHTML = '';
        document.getElementById('sobras-quick-actions')?.classList.add('hidden');

        hideOverlay();
        showNotification('Pronto para conciliar com os itens sobrando.', 'info');
    } else {
        // Se savePendingLinks falhar, hideOverlay já foi chamado lá
        console.log("Finalização cancelada devido a erro ao salvar vínculos pendentes.");
    }
}

function handleDeleteCreatedLink(e) {
    const deleteBtn = e.target.closest('.delete-link-btn');
    if (!deleteBtn) return;

    const index = parseInt(deleteBtn.dataset.index, 10);
    const removedLink = linksToCreate.splice(index, 1)[0];

    if (removedLink) {
        const systemEl = document.querySelector(`#system-list div[data-id='${removedLink.systemItem.id}']`);
        if (systemEl) systemEl.classList.remove('linked');
        const giapEl = document.querySelector(`#giap-list div[data-id='${removedLink.giapItem.TOMBAMENTO}']`);
        if (giapEl) giapEl.classList.remove('linked');
    }
    renderCreatedLinks('unidade');
    showNotification('Vínculo removido.', 'info');
}

async function handleImportGiapItems() {
     // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
     if (auth.currentUser?.isAnonymous) {
         showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
         return;
     }

     if (giapItemsForImport.length === 0) return showNotification('Nenhum item GIAP selecionado para importar.', 'warning');

    const tipo = activeConciliationType;
    const unidade = activeConciliationUnit;
    if (!unidade || !tipo) return showNotification('Por favor, carregue uma unidade primeiro antes de importar.', 'warning');

    const estadoEl = document.getElementById('import-estado-select');
    const estado = estadoEl ? estadoEl.value : 'Regular'; // Fallback


    showOverlay(`Importando ${giapItemsForImport.length} itens...`);
    const batch = writeBatch(db);
    const newItemsForCache = [];

    giapItemsForImport.forEach(giapItem => {
        // MUDANÇA: Usa a coleção correta no Firebase
        const patrimonioCollectionRef = collection(db, getCollectionPath('patrimonio'));
        const newItemRef = doc(patrimonioCollectionRef); // Gera ID localmente
        const newItem = {
            id: newItemRef.id, // Adiciona o ID para cache
            Tombamento: giapItem.TOMBAMENTO || '', Descrição: giapItem.Descrição || giapItem.Espécie || '',
            Tipo: tipo, Unidade: unidade, Localização: '',
            Fornecedor: giapItem['Nome Fornecedor'] || '', NF: giapItem.NF || '', 'Origem da Doação': '',
            Estado: estado, Quantidade: 1, Observação: `Importado do GIAP. Unidade original: ${giapItem.Unidade || 'N/A'}`,
            etiquetaPendente: true, isPermuta: false,
            createdAt: serverTimestamp(), updatedAt: serverTimestamp()
        };
        batch.set(newItemRef, newItem);
        newItemsForCache.push(newItem); // Adiciona ao array para cache
    });

    try {
        await batch.commit();

        // Adiciona novos itens ao cache local e ao array principal
        fullInventory.push(...newItemsForCache);
        await idb.patrimonio.bulkAdd(newItemsForCache);

        showNotification(`${giapItemsForImport.length} itens importados com sucesso! Atualizando...`, 'success');
        clearGiapImportSelection();

        renderConciliationLists(); // Re-renderiza localmente
        hideOverlay();

    } catch (e) {
        hideOverlay();
        showNotification('Erro ao importar itens.', 'error');
        console.error(e);
    }
}

function handleConciliationSubTabSwitch(e) {
    const subTab = e.currentTarget.dataset.subtabConciliar;
    document.querySelectorAll('#content-conciliar .sub-nav-btn').forEach(btn => btn.classList.toggle('active', btn.dataset.subtabConciliar === subTab));
    document.getElementById('subtab-conciliar-unidade').classList.toggle('hidden', subTab !== 'conciliacao_unidade');
    document.getElementById('subtab-conciliar-sobras').classList.toggle('hidden', subTab !== 'conciliacao_sobras');
    document.getElementById('subtab-conciliar-itens_a_tombar').classList.toggle('hidden', subTab !== 'itens_a_tombar');

    linksToCreate = []; selSys = null; selGiap = null; // Limpa estado ao trocar sub-aba

    if(subTab === 'itens_a_tombar') {
        if (!initializedTabs.has('itens_a_tombar')) { // Inicializa se for a primeira vez
             populateTombarTabFilters(); // Popula filtros antes de renderizar
            renderItensATombar();
            initializedTabs.add('itens_a_tombar');
        } else {
             renderItensATombar(); // Sempre re-renderiza para dados atualizados
        }
    } else if (subTab === 'conciliacao_sobras') {
         if (!initializedTabs.has('conciliacao_sobras')) {
            populateSobrantesTab(); // Popula os filtros
            initializedTabs.add('conciliacao_sobras');
         } else {
             populateSobrantesTab(); // Apenas repopula os filtros
         }
         // Limpa listas ao trocar PARA esta aba
         document.getElementById('sobras-system-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione Tipo e Unidade e clique em Carregar.</p>`;
         document.getElementById('sobras-giap-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Os tombos sobrando aparecerão aqui.</p>`;
         document.getElementById('sobras-created-links').innerHTML = '';
         document.getElementById('sobras-quick-actions')?.classList.add('hidden');
    } else { // unidade
         if (!initializedTabs.has('conciliacao_unidade')) {
             // A aba unidade já é populada pelo initReconciliationTab principal
             initializedTabs.add('conciliacao_unidade');
         } else {
             // Repopula filtros da aba unidade ao voltar para ela
             populateReconciliationTab();
         }
         // Limpa listas ao trocar PARA esta aba
         document.getElementById('system-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione uma unidade e clique em carregar.</p>`;
         document.getElementById('giap-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione uma unidade e clique em carregar.</p>`;
         document.getElementById('created-links').innerHTML = '';
         document.getElementById('quick-actions')?.classList.add('hidden');
    }
}

// Handler para popular filtros da aba "Itens a Tombar"
function populateTombarTabFilters() {
     const tipos = [...new Set((fullInventory || []).filter(i => i && i.etiquetaPendente === true).map(i => i.Tipo).filter(Boolean))].sort(); // Fallback e checagem item
     const tipoSelect = document.getElementById('tombar-filter-tipo');
     if(tipoSelect) tipoSelect.innerHTML = '<option value="">Todos os Tipos</option>' + tipos.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');

     const unidadeSelect = document.getElementById('tombar-filter-unidade');
     if(unidadeSelect) {
         unidadeSelect.innerHTML = '<option value="">Selecione um Tipo</option>';
         unidadeSelect.disabled = true;
     }
}


// Handlers da Aba Itens a Tombar
function handleTombarFilterChange() {
    const tipo = document.getElementById('tombar-filter-tipo').value;
    const unidades = [...new Set((fullInventory || []) // Fallback
        .filter(i => i && i.etiquetaPendente === true && (!tipo || i.Tipo === tipo)) // Checagem item
        .map(i => i.Unidade).filter(Boolean))].sort();
    const selU = document.getElementById('tombar-filter-unidade');
    if(selU) {
        selU.innerHTML = '<option value="">Todas as Unidades</option>' + unidades.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`).join('');
        selU.disabled = false;
    }
    renderItensATombar();
}

async function handleConfirmTombamento(e) {
     // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
     if (auth.currentUser?.isAnonymous) {
         showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
         return;
     }

    const btn = e.target.closest('.confirmar-tombamento-btn');
    if (!btn) return;
    const id = btn.dataset.id;
    btn.disabled = true;
    btn.textContent = 'Salvando...';
    try {
        // MUDANÇA: Usa a coleção correta no Firebase
        const docRef = doc(db, getCollectionPath('patrimonio'), id);
        await updateDoc(docRef, { etiquetaPendente: false });
        const itemInInventory = fullInventory.find(i => i.id === id);
        if(itemInInventory) itemInInventory.etiquetaPendente = false;
        await idb.patrimonio.update(id, { etiquetaPendente: false });
        showNotification('Tombamento confirmado!', 'success');
        renderItensATombar(); // Re-renderiza a lista atualizada
    } catch (error) {
        console.error('Erro ao confirmar tombamento:', error);
        showNotification('Erro ao confirmar.', 'error');
        btn.disabled = false;
        btn.textContent = 'Confirmar Tombamento';
    }
}

// Handlers da Aba Transferências
async function handleTransferAction(e) {
     // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
     if (auth.currentUser?.isAnonymous) {
         showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
         return;
     }

    const target = e.target;
    if (target.classList.contains('select-all-in-unit')) {
        const detailsContent = target.closest('details');
        const checkboxes = detailsContent.querySelectorAll('.transfer-item-checkbox');
        checkboxes.forEach(cb => cb.checked = target.checked);
        return;
    }
    const actionButton = target.closest('.keep-selected-btn, .transfer-selected-btn');
    if (!actionButton) return;
    const detailsContent = actionButton.closest('details');
    const selectedCheckboxes = detailsContent.querySelectorAll('.transfer-item-checkbox:checked');
    if (selectedCheckboxes.length === 0) {
        showNotification('Nenhum item selecionado para a ação.', 'warning');
        return;
    }
    const batch = writeBatch(db);
    let actionDescription = '';
    const itemsToUpdateLocally = []; // Para atualizar cache

    if (actionButton.classList.contains('keep-selected-btn')) {
        actionDescription = `Mantendo ${selectedCheckboxes.length} iten(s) na unidade de origem...`;
        selectedCheckboxes.forEach(cb => {
            // MUDANÇA: Usa a coleção correta no Firebase
            const docRef = doc(db, getCollectionPath('patrimonio'), cb.dataset.id);
            const updateData = { Observação: 'Transferência GIAP ignorada manualmente.', updatedAt: serverTimestamp() };
            batch.update(docRef, updateData);
            itemsToUpdateLocally.push({ id: cb.dataset.id, changes: { Observação: 'Transferência GIAP ignorada manualmente.' } });
        });
    } else if (actionButton.classList.contains('transfer-selected-btn')) {
        actionDescription = `Transferindo ${selectedCheckboxes.length} iten(s)...`;
        selectedCheckboxes.forEach(cb => {
            // MUDANÇA: Usa a coleção correta no Firebase
            const docRef = doc(db, getCollectionPath('patrimonio'), cb.dataset.id);
            const newUnit = cb.dataset.giapUnit;
            // Tenta encontrar o tipo da nova unidade
            const existingItemInNewUnit = fullInventory.find(i => i.Unidade === newUnit);
            const newTipo = existingItemInNewUnit ? existingItemInNewUnit.Tipo : 'N/A (Verificar)';
            const updateData = { Unidade: newUnit, Tipo: newTipo, Observação: 'Item transferido para unidade correta via auditoria.', updatedAt: serverTimestamp() };
            batch.update(docRef, updateData);
            itemsToUpdateLocally.push({ id: cb.dataset.id, changes: { Unidade: newUnit, Tipo: newTipo, Observação: 'Item transferido para unidade correta via auditoria.' } });
        });
    }

    showOverlay(actionDescription);
    try {
        await batch.commit();
        // Atualiza cache
        await idb.transaction('rw', idb.patrimonio, async () => {
             for (const update of itemsToUpdateLocally) {
                 await idb.patrimonio.update(update.id, update.changes);
             }
        });
        // Atualiza array principal
        itemsToUpdateLocally.forEach(update => {
             const index = fullInventory.findIndex(i => i.id === update.id);
             if (index > -1) {
                 fullInventory[index] = { ...fullInventory[index], ...update.changes };
             }
        });
        showNotification('Ação concluída com sucesso! Atualizando visualização...', 'success');
        populatePendingTransfersTab(); // Re-renderiza a aba
    } catch (error) {
        showNotification('Ocorreu um erro ao processar a solicitação.', 'error');
        console.error("Erro na ação de transferência:", error);
    } finally {
        hideOverlay();
    }
}

// Handlers da Aba Importação
function handleImportSubTabSwitch(e) {
    const subTab = e.currentTarget.dataset.subtab;
    document.querySelectorAll('#content-importacao .sub-nav-btn').forEach(btn => btn.classList.toggle('active', btn.dataset.subtab === subTab));
    document.getElementById('subtab-content-substituir').classList.toggle('hidden', subTab !== 'substituir');
    document.getElementById('subtab-content-edit-by-desc').classList.toggle('hidden', subTab !== 'edit-by-desc');
    document.getElementById('subtab-content-massa').classList.toggle('hidden', subTab !== 'massa');
    document.getElementById('subtab-content-add_giap').classList.toggle('hidden', subTab !== 'add_giap');
}

function handlePreviewReplace() {
    const data = document.getElementById('replace-data').value;
    const unit = document.getElementById('replace-unit').value;
    if (!unit) return showNotification('Selecione uma unidade de destino primeiro.', 'warning');
    if (!data) return showNotification('Cole os dados da planilha na área de texto.', 'warning');

    Papa.parse(data, {
        header: false,
        skipEmptyLines: true,
        complete: (results) => {
             if (results.errors.length > 0) {
                 console.error("PapaParse errors:", results.errors);
                 showNotification(`Erro ao ler dados colados (linha ${results.errors[0].row}). Verifique o formato.`, 'error');
                 return;
             }
            itemsToReplace = results.data.map(row => ({
                UNIDADE_EXCEL: (row[0] || '').trim(),
                ITEM: (row[1] || '').trim(),
                TOMBO: (row[2] || '').trim(),
                LOCAL: (row[3] || '').trim(),
                ESTADO: (row[4] || '').trim()
            })).filter(item => item.ITEM); // Filtra linhas sem descrição de item

            const previewList = document.getElementById('replace-preview-list');
            const countEl = document.getElementById('replace-preview-count');
            if (countEl) countEl.textContent = itemsToReplace.length;
            if (previewList) {
                previewList.innerHTML = itemsToReplace.map(item => `
                    <div class="p-2 border-b text-xs">
                        <strong>${escapeHtml(item.ITEM)}</strong> (Tombo: ${escapeHtml(item.TOMBO) || 'S/T'})<br>
                        Local: ${escapeHtml(item.LOCAL)} | Estado: ${escapeHtml(item.ESTADO)}
                    </div>
                `).join('');
            }
             const resultsDiv = document.getElementById('replace-results');
             if (resultsDiv) resultsDiv.classList.remove('hidden');

            // Reseta e desabilita botão de confirmação
            const checkbox = document.getElementById('replace-confirm-checkbox');
            const confirmBtn = document.getElementById('confirm-replace-btn');
            if (checkbox) checkbox.checked = false;
            if (confirmBtn) confirmBtn.disabled = true;
        },
        error: (err) => {
            showNotification('Erro ao processar os dados. Verifique o formato.', 'error');
            console.error(err);
             const resultsDiv = document.getElementById('replace-results');
             if(resultsDiv) resultsDiv.classList.add('hidden');
        }
    });
}

function handleReplaceConfirmChange(e) {
     const confirmBtn = document.getElementById('confirm-replace-btn');
     // MUDANÇA: Desabilita se for anônimo
     confirmBtn.disabled = !e.target.checked || auth.currentUser?.isAnonymous;
}

async function handleConfirmReplace() {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }

    const tipo = document.getElementById('replace-tipo').value;
    const unidade = document.getElementById('replace-unit').value.trim();

    if (!unidade || itemsToReplace.length === 0) return showNotification('Dados inválidos ou unidade não selecionada.', 'error');

    showOverlay(`Substituindo inventário de ${unidade}...`);
    const itemsToDelete = fullInventory.filter(item => item.Unidade.trim() === unidade);
    const idsToDelete = itemsToDelete.map(item => item.id);

    const batch = writeBatch(db);

    itemsToDelete.forEach(item => {
        // MUDANÇA: Usa a coleção correta no Firebase
        const docRef = doc(db, getCollectionPath('patrimonio'), item.id);
        batch.delete(docRef);
    });

    const newItemsAdded = []; // Para atualizar cache e array
    itemsToReplace.forEach(item => {
        // MUDANÇA: Usa a coleção correta no Firebase
        const patrimonioCollectionRef = collection(db, getCollectionPath('patrimonio'));
        const newItemRef = doc(patrimonioCollectionRef);
        const { estado, origem } = parseEstadoEOrigem(item.ESTADO);
        const newItemData = {
            Unidade: unidade, Tipo: tipo,
            Descrição: item.ITEM || '', Tombamento: item.TOMBO || 'S/T',
            Localização: item.LOCAL || '',
            Estado: estado,
            'Origem da Doação': origem,
            Quantidade: 1, Fornecedor: '', NF: '',
            Observação: 'Importado via substituição de planilha.',
            etiquetaPendente: (item.TOMBO && item.TOMBO.toLowerCase() !== 's/t'),
            isPermuta: false,
            createdAt: serverTimestamp(), updatedAt: serverTimestamp()
        };
        batch.set(newItemRef, newItemData);
        newItemsAdded.push({ ...newItemData, id: newItemRef.id }); // Adiciona com ID para cache
    });

    try {
        await batch.commit();
        // Atualiza cache e array principal
        await idb.patrimonio.bulkDelete(idsToDelete);
        await idb.patrimonio.bulkAdd(newItemsAdded);
        fullInventory = fullInventory.filter(item => item.Unidade.trim() !== unidade);
        fullInventory.push(...newItemsAdded);

        showNotification(`Inventário de ${unidade} substituído com sucesso! Atualizando...`, 'success');
        // Limpa a UI da aba
        document.getElementById('replace-data').value = '';
        document.getElementById('replace-results').classList.add('hidden');
        document.getElementById('replace-confirm-checkbox').checked = false;
        document.getElementById('confirm-replace-btn').disabled = true;
        itemsToReplace = [];
        // Repopula selects em outras abas que podem ter sido afetadas
        initializedTabs.clear(); // Força reinicialização de todas as abas
        dataLoaded = false; // Força recarregamento completo dos dados
        await loadData(true); // Recarrega do servidor

    } catch(e) {
        showNotification('Erro ao substituir o inventário.', 'error');
        console.error(e);
    } finally {
        hideOverlay();
    }
}

function handlePreviewEditByDesc() {
     const unidade = document.getElementById('edit-by-desc-unit').value;
    const data = document.getElementById('edit-by-desc-data').value;
    if (!unidade) return showNotification('Selecione uma unidade de destino.', 'warning');
    if (!data) return showNotification('Cole os dados da planilha.', 'warning');

    const mappedGiapUnits = (unitMapping[unidade] || [unidade]).map(u => normalizeStr(u));

    Papa.parse(data, {
        header: true,
        skipEmptyLines: true,
        transformHeader: (h) => {
            const normH = normalizeStr(h);
            if (normH.includes('item') || normH.includes('descri')) return 'descricao';
            if (normH.includes('tombo') || normH.includes('tombamento')) return 'tombamento';
            if (normH.includes('local')) return 'localizacao';
            if (normH.includes('estado')) return 'estado';
            return h;
        },
        complete: (results) => {
            if (results.errors.length > 0) {
                 showNotification('Erro ao ler cabeçalhos da planilha. Verifique nomes das colunas.', 'error');
                 console.error("PapaParse errors:", results.errors);
                 return;
            }
            const pastedData = results.data;
            const inventoryInUnit = (fullInventory || []).filter(i => i.Unidade === unidade); // Fallback
            const existingTombos = new Map((fullInventory || []).map(i => i ? [normalizeTombo(i.Tombamento), i] : null).filter(Boolean)); // Fallback

            const availableItems = inventoryInUnit.map(item => ({ item, isMatched: false }));

            updatesToProcess = pastedData.map((row, rowIndex) => {
                const pastedDesc = (row.descricao || '').trim();
                const pastedTomboRaw = (row.tombamento || 'S/T').trim();
                const pastedTombo = normalizeTombo(pastedTomboRaw);
                const pastedLocal = (row.localizacao || '').trim();
                const { estado: pastedEstado } = parseEstadoEOrigem((row.estado || '').trim()); // Apenas o estado

                if (!pastedDesc && !pastedTomboRaw && !pastedLocal && !(row.estado || '').trim()) {
                    return { id: rowIndex, status: 'empty_row' }; // Ignora linha completamente vazia
                }
                 if (!pastedDesc) {
                     // Considera erro se não houver descrição, pois é a chave primária da busca
                     return { id: rowIndex, status: 'missing_desc', pastedData: { descricao: '', tombamento: pastedTombo, localizacao: pastedLocal, estado: pastedEstado } };
                 }

                const pastedItemForMatching = { descricao: pastedDesc, localizacao: pastedLocal, estado: pastedEstado };
                const { wrapper: bestMatchWrapper, matchType } = findBestMatchForItem(pastedItemForMatching, availableItems);

                const systemItem = bestMatchWrapper ? bestMatchWrapper.item : null;
                const giapItem = pastedTombo ? giapMapAllItems.get(pastedTombo) : null; // Usa giapMapAllItems para checar existência
                const tomboInUse = pastedTombo && pastedTombo !== 'S/T' && existingTombos.has(pastedTombo) && existingTombos.get(pastedTombo).id !== systemItem?.id;

                let tomboWrongLocation = false;
                if (giapItem) {
                    const giapUnitForTombo = normalizeStr(giapItem.Unidade);
                    if (!mappedGiapUnits.includes(giapUnitForTombo)) {
                        tomboWrongLocation = true;
                    }
                }

                let status = 'ok';
                if (!systemItem) {
                    status = 'not_found';
                } else if (matchType.includes('Ambigua')) {
                    status = 'multiple_found';
                } else if (tomboInUse) {
                    status = 'tombo_in_use';
                } else if (tomboWrongLocation) {
                    status = 'tombo_wrong_location';
                } else if (!pastedTombo || pastedTombo === 'S/T') {
                    // Se não tem tombo na planilha, não considera erro, apenas não atualiza tombo
                } else if (!giapItem) {
                     // Tombo existe na planilha mas não no GIAP
                    status = 'tombo_not_in_giap'; // Novo status
                }


                return {
                    id: rowIndex,
                    pastedData: { descricao: pastedDesc, tombamento: pastedTombo, localizacao: pastedLocal, estado: pastedEstado },
                    systemItem, giapItem, status, matchType, useGiapDesc: false,
                };
            }).filter(u => u.status !== 'empty_row');

            renderEditByDescPreview(updatesToProcess);
             const resultsDiv = document.getElementById('edit-by-desc-results');
             const confirmBtn = document.getElementById('confirm-edit-by-desc-btn');
             const countEl = document.getElementById('edit-by-desc-preview-count');

             if (resultsDiv) resultsDiv.classList.remove('hidden');
            const validCount = updatesToProcess.filter(u => u.status === 'ok' || u.status === 'tombo_not_in_giap').length;
             // MUDANÇA: Desabilita se for anônimo
             if (confirmBtn) confirmBtn.disabled = validCount === 0 || auth.currentUser?.isAnonymous;
             if (countEl) countEl.textContent = `${updatesToProcess.length} (Válidos para salvar: ${validCount})`;


        },
         error: (err) => {
            showNotification('Erro ao processar dados. Verifique formato e cabeçalhos.', 'error');
            console.error(err);
             const resultsDiv = document.getElementById('edit-by-desc-results');
             if (resultsDiv) resultsDiv.classList.add('hidden');
        }
    });
}

function renderEditByDescPreview(updates) {
    // Função auxiliar para determinar a classe CSS da linha
    const getRowClass = (status) => {
        switch (status) {
            case 'ok': return 'bg-white hover:bg-slate-50';
            case 'not_found': return 'bg-yellow-100 hover:bg-yellow-200';
            case 'multiple_found': return 'bg-yellow-200 hover:bg-yellow-300';
            case 'tombo_in_use': return 'bg-red-100 hover:bg-red-200';
            case 'tombo_wrong_location': return 'bg-orange-100 hover:bg-orange-200';
            case 'tombo_not_in_giap': return 'bg-blue-100 hover:bg-blue-200'; // Novo estilo
            case 'missing_desc': return 'bg-red-200 hover:bg-red-300';
            default: return 'bg-slate-100';
        }
    };

    // Função auxiliar para determinar o ícone de status
    const getStatusIcon = (status) => {
        switch (status) {
            case 'ok': return '✅ OK';
            case 'not_found': return '⚠️ Não Encontrado';
            case 'multiple_found': return '⚠️ Correspondência Ambigua';
            case 'tombo_in_use': return '❌ Tombo em Uso em Outro Item';
            case 'tombo_wrong_location': return '🟠 Tombo Pertence a Outra Unidade GIAP';
            case 'tombo_not_in_giap': return '🔵 Tombo Não Existe no GIAP';
            case 'missing_desc': return '❌ Descrição Faltando';
            default: return '❓ Erro Desconhecido';
        }
    };

    // Começa a construção da tabela
    let tableHtml = `
        <table class="w-full text-sm border-collapse">
            <thead class="bg-gradient-to-r from-slate-100 to-slate-200 sticky top-0 z-10 shadow-sm">
                <tr>
                    <th class="px-3 py-2 text-left w-1/12">Status</th>
                    <th class="px-3 py-2 text-left w-2/12">Item do Sistema</th>
                    <th class="px-3 py-2 text-left w-2/12">Tombo Planilha</th>
                    <th class="px-3 py-2 text-left w-2/12">Nova Localização/Estado</th>
                    <th class="px-3 py-2 text-left w-2/12">Tombo Destino</th>
                    <th class="px-3 py-2 text-left w-2/12">Desc. GIAP (Se Houver)</th>
                    <th class="px-3 py-2 text-center w-1/12">Usar Desc. GIAP</th>
                </tr>
            </thead>
            <tbody id="edit-by-desc-table-body">
    `;

    updates.forEach(update => {
        const rowClass = getRowClass(update.status);
        const tomboDisplay = update.pastedData.tombamento || 'S/T';
        const tomboDestino = update.systemItem ? update.systemItem.Tombamento || 'S/T' : 'N/A';
        const descSistema = update.systemItem ? update.systemItem.Descrição || 'N/A' : 'N/A';
        const descGiap = update.giapItem ? update.giapItem.Descrição || update.giapItem.Espécie : 'N/A';
        const isEditable = update.systemItem && (update.status === 'ok' || update.status === 'tombo_not_in_giap');
        const showGiapDescOption = isEditable && update.giapItem && descGiap !== 'N/A';
        const isTomboChanged = isEditable && update.pastedData.tombamento !== tomboDestino;
        const isLocalChanged = isEditable && update.pastedData.localizacao !== update.systemItem.Localização;
        const isEstadoChanged = isEditable && update.pastedData.estado !== update.systemItem.Estado;


        tableHtml += `
            <tr class="${rowClass} border-b text-xs">
                <td class="px-3 py-2 text-xs font-semibold">${getStatusIcon(update.status)}</td>
                <td class="px-3 py-2">${escapeHtml(descSistema)} (${update.matchType})</td>
                <td class="px-3 py-2 ${isTomboChanged ? 'font-bold text-blue-700' : ''}">${escapeHtml(tomboDisplay)}</td>
                <td class="px-3 py-2">
                    <span class="${isLocalChanged ? 'font-bold text-blue-700' : ''}">${escapeHtml(update.pastedData.localizacao || 'N/A')}</span> / 
                    <span class="${isEstadoChanged ? 'font-bold text-blue-700' : ''}">${escapeHtml(update.pastedData.estado || 'N/A')}</span>
                </td>
                <td class="px-3 py-2 font-mono">${escapeHtml(tomboDestino)}</td>
                <td class="px-3 py-2 text-slate-600">${escapeHtml(descGiap)}</td>
                <td class="px-3 py-2 text-center">
                    ${showGiapDescOption ? `
                        <input type="checkbox" data-update-id="${update.id}" class="h-4 w-4 use-giap-desc-cb text-blue-600 border-gray-300 rounded focus:ring-blue-500">
                    ` : 'N/A'}
                </td>
            </tr>
        `;
    });

    tableHtml += `</tbody></table>`;
    document.getElementById('edit-by-desc-preview-table-container').innerHTML = tableHtml;
}

function handleEditByDescCheckboxChange(e) {
     const checkbox = e.target;
    if (checkbox.classList.contains('use-giap-desc-cb')) {
        const updateId = parseInt(checkbox.dataset.updateId, 10);
        const update = updatesToProcess.find(u => u.id === updateId);
        if (update) {
            update.useGiapDesc = checkbox.checked;
        }
    }
}

async function handleConfirmEditByDesc() {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }

    const validUpdates = updatesToProcess.filter(u => u.status === 'ok' || u.status === 'tombo_not_in_giap'); // Inclui tombo_not_in_giap
    if(validUpdates.length === 0) return showNotification('Nenhum item válido para atualizar.', 'error');

    showOverlay(`Atualizando ${validUpdates.length} itens...`);
    const batch = writeBatch(db);
    const itemsToUpdateLocally = [];

    validUpdates.forEach(upd => {
        // MUDANÇA: Usa a coleção correta no Firebase
        const docRef = doc(db, getCollectionPath('patrimonio'), upd.systemItem.id);
        const updatePayload = {
            // Tombamento SÓ é atualizado se for válido (não S/T e não 'tombo_not_in_giap')
            ...(upd.pastedData.tombamento && upd.pastedData.tombamento !== 'S/T' && upd.status !== 'tombo_not_in_giap' && { Tombamento: upd.pastedData.tombamento }),
            Localização: upd.pastedData.localizacao,
            Estado: upd.pastedData.estado,
            updatedAt: serverTimestamp()
        };


        if (upd.useGiapDesc && upd.giapItem) {
            const giapDesc = upd.giapItem.Descrição || upd.giapItem.Espécie;
            if(giapDesc) {
               updatePayload.Descrição = giapDesc;
            }
        }

        // Marca para etiqueta apenas se o tombo for válido e não S/T
        if(upd.pastedData.tombamento && upd.pastedData.tombamento.toLowerCase() !== 's/t' && upd.status !== 'tombo_not_in_giap') {
            updatePayload.etiquetaPendente = true;
        }

        batch.update(docRef, updatePayload);
        itemsToUpdateLocally.push({ id: upd.systemItem.id, changes: updatePayload });
    });

    try {
        await batch.commit();
         // Atualiza cache e array principal
        await idb.transaction('rw', idb.patrimonio, async () => {
             for (const update of itemsToUpdateLocally) {
                 await idb.patrimonio.update(update.id, update.changes);
             }
        });
        itemsToUpdateLocally.forEach(update => {
             const index = fullInventory.findIndex(i => i.id === update.id);
             if (index > -1) {
                 // Aplica as mudanças ao item existente no array principal
                 fullInventory[index] = { ...fullInventory[index], ...update.changes };
             }
        });


        showNotification(`${validUpdates.length} itens atualizados com sucesso! Atualizando visualização...`, 'success');
        // Limpa a UI da aba
        document.getElementById('edit-by-desc-data').value = '';
        document.getElementById('edit-by-desc-results').classList.add('hidden');
        updatesToProcess = [];
         // Repopula selects e reinicializa abas afetadas
         initializedTabs.clear(); // Força reinicialização de todas as abas
         dataLoaded = false; // Força recarregamento completo dos dados
         await loadData(true); // Recarrega do servidor

    } catch(e) {
        showNotification('Erro ao atualizar os itens.', 'error');
        console.error(e);
    } finally {
         hideOverlay();
    }
}


function handleMassTransferSearch() {
    const tombosInputEl = document.getElementById('mass-transfer-tombos');
    if (!tombosInputEl) return; // Verifica
    const tombosInput = tombosInputEl.value;
    const tombos = tombosInput.split(/[\s,]+/).map(t => normalizeTombo(t.trim())).filter(Boolean); // Normaliza aqui
    const existingTombos = new Set((fullInventory || []).map(i => i ? normalizeTombo(i.Tombamento) : null).filter(Boolean)); // Fallback e checagem item // Normaliza aqui
    const foundItems = []; const notFound = [];
    tombos.forEach(tombo => {
        const giapItem = giapMap.get(tombo); // Já busca normalizado
        if (giapItem && !existingTombos.has(tombo)) foundItems.push(giapItem);
        else notFound.push(tombo);
    });
    if (notFound.length > 0) showNotification(`Não encontrados ou já existem: ${notFound.join(', ')}`, 'warning', 5000);
    const massTransferResults = document.getElementById('mass-transfer-results');
    const massTransferList = document.getElementById('mass-transfer-list');
    if (massTransferResults && massTransferList) {
        if (foundItems.length > 0) {
            const estadoOptions = ['Novo', 'Bom', 'Regular', 'Avariado'];
            massTransferList.innerHTML = foundItems.map(item => `
                <div class="p-2 border rounded-md bg-slate-50 grid grid-cols-3 gap-4 items-center">
                    <div class="col-span-2"><strong>${escapeHtml(item.TOMBAMENTO)}</strong> - ${escapeHtml(item.Descrição || item.Espécie)}</div>
                    <div><select data-tombo="${escapeHtml(item.TOMBAMENTO)}" class="mass-transfer-status w-full p-1 border rounded bg-white">${estadoOptions.map(opt => `<option>${opt}</option>`).join('')}</select></div>
                </div>`).join('');
            massTransferResults.classList.remove('hidden');
        } else {
            massTransferList.innerHTML = ''; // Limpa a lista se não houver itens
            massTransferResults.classList.add('hidden');
        }
    }
}


function handleMassTransferSetAllStatus(e) {
    document.querySelectorAll('.mass-transfer-status').forEach(select => select.value = e.target.value);
}

async function handleMassTransferConfirm() {
    // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
    if (auth.currentUser?.isAnonymous) {
        showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
        return;
    }

    const massTransferUnitEl = document.getElementById('mass-transfer-unit');
    const massTransferTipoEl = document.getElementById('mass-transfer-tipo');
     if (!massTransferUnitEl || !massTransferTipoEl) return; // Verifica

    const destinationUnit = massTransferUnitEl.value;
    const destinationTipo = massTransferTipoEl.value;
    if (!destinationUnit) return showNotification('Selecione uma unidade de destino.', 'warning');
    if (!destinationTipo) return showNotification('Selecione um tipo de unidade de destino.', 'warning');

    const itemsToCreateElements = Array.from(document.querySelectorAll('.mass-transfer-status'));
    if (itemsToCreateElements.length === 0) return;

    showOverlay(`Criando ${itemsToCreateElements.length} itens...`);
    const batch = writeBatch(db);
    const newItemsForCache = []; // Para atualizar localmente

    itemsToCreateElements.forEach(select => {
        const tombo = select.dataset.tombo;
        const giapItem = giapMap.get(tombo); // Busca normalizado
        if (giapItem) {
            // MUDANÇA: Usa a coleção correta no Firebase
            const patrimonioCollectionRef = collection(db, getCollectionPath('patrimonio'));
            const newItemRef = doc(patrimonioCollectionRef);
            const newItem = {
                id: newItemRef.id, // Adiciona ID para cache
                Tombamento: tombo, Descrição: giapItem.Descrição || giapItem.Espécie || '',
                Tipo: destinationTipo, Unidade: destinationUnit, Localização: '',
                Fornecedor: giapItem['Nome Fornecedor'] || '', NF: giapItem.NF || '', 'Origem da Doação': '',
                Estado: select.value, Quantidade: 1, Observação: `Importado em massa. Unidade GIAP: ${giapItem.Unidade || 'N/A'}`,
                etiquetaPendente: true, isPermuta: false,
                createdAt: serverTimestamp(), updatedAt: serverTimestamp()
            };
            batch.set(newItemRef, newItem);
            newItemsForCache.push(newItem);
        }
    });
    try {
        await batch.commit();
        // Atualiza cache e array principal
        fullInventory.push(...newItemsForCache);
        await idb.patrimonio.bulkAdd(newItemsForCache);

        showNotification(`${itemsToCreateElements.length} itens criados com sucesso! Atualizando...`, 'success');
         // Limpa a UI da aba
        document.getElementById('mass-transfer-tombos').value = '';
        document.getElementById('mass-transfer-results').classList.add('hidden');
        document.getElementById('mass-transfer-list').innerHTML = '';
         // Repopula selects e reinicializa abas afetadas
         initializedTabs.clear(); // Força reinicialização de todas as abas
         dataLoaded = false; // Força recarregamento completo dos dados
         await loadData(true); // Recarrega do servidor

    } catch (e) {
        showNotification('Erro ao criar itens em massa.', 'error');
        console.error(e);
    } finally {
        hideOverlay();
    }
}

async function handleSaveGiapUnit() {
     // MUDANÇA: Bloqueia ações de escrita para usuários anônimos
     if (auth.currentUser?.isAnonymous) {
         showNotification('Acesso negado. Ações de escrita são apenas para usuários autenticados.', 'error');
         return;
     }

     const nameInput = document.getElementById('add-giap-name');
     const numberInput = document.getElementById('add-giap-number');
     if (!nameInput || !numberInput) return; // Verifica

    const newUnitName = nameInput.value.trim();
    const newUnitNumber = numberInput.value.trim();
    if (!newUnitName) {
        return showNotification('O nome da unidade não pode ser vazio.', 'warning');
    }

    const normalizedNewName = normalizeStr(newUnitName);
    const allGiapUnitNames = new Set((giapInventory || []).map(i => i ? normalizeStr(i.Unidade) : null).filter(Boolean)); // Fallback
    const allCustomUnitNames = new Set(customGiapUnits.map(u => normalizeStr(u.name)));

    if (allGiapUnitNames.has(normalizedNewName) || allCustomUnitNames.has(normalizedNewName)) {
        return showNotification('Esta unidade já existe.', 'error');
    }

    showOverlay('Salvando nova unidade...');
    const updatedCustomUnits = [...customGiapUnits, { name: newUnitName, number: newUnitNumber }];

    try {
        // MUDANÇA: Usa a coleção correta no Firebase
        const docRef = doc(db, getCollectionPath('config'), 'customGiapUnits');
        await setDoc(docRef, { units: updatedCustomUnits });
        customGiapUnits.push({ name: newUnitName, number: newUnitNumber });
        showNotification('Nova unidade salva com sucesso!', 'success');
        nameInput.value = '';
        numberInput.value = '';
        updateGiapUnitOptions(); // Refresh the list na aba Ligar Unidades
    } catch(e) {
        showNotification('Erro ao salvar a nova unidade.', 'error');
        console.error(e);
    } finally {
        hideOverlay();
    }
}

// Handlers da Aba NF
function handleClearNfFilters() {
    document.getElementById('nf-search').value = '';
    document.getElementById('nf-item-search').value = '';
    document.getElementById('nf-fornecedor-search').value = '';
    document.getElementById('nf-tipo-entrada').value = '';
    document.getElementById('nf-status-filter').value = '';
    document.getElementById('nf-date-start').value = '';
    document.getElementById('nf-date-end').value = '';
    renderNfList();
}


// --- FIM DOS HANDLERS ---


// --- INICIALIZAÇÃO GERAL ---
document.addEventListener('DOMContentLoaded', () => {
    initDomElements(); // Cache DOM elements first

    // Adiciona listener de autenticação APRIMORADO (sem delay, sem authReady)
    addAuthListener(user => {
        // MUDANÇA: Agora precisamos verificar se o usuário NÃO é anônimo para ter acesso à edição
        const isUserAdmin = user && !user.isAnonymous;

        if (isUserAdmin) {
            // --- USUÁRIO ESTÁ LOGADO (ADMIN) ---
            console.log("Auth state: Logged In (Admin)");
            if (domCache.userEmailEdit) domCache.userEmailEdit.textContent = user.email;

            if (domCache.authGate) domCache.authGate.classList.add('hidden');
            
            if (!dataLoaded) {
                console.log("User logged in, data not loaded. Fetching data...");
                if (domCache.loadingScreen) domCache.loadingScreen.classList.remove('hidden');
                if (domCache.feedbackStatus) domCache.feedbackStatus.textContent = "Usuário autenticado. Carregando dados...";
                loadData(false); // Chama loadData, que agora é responsável por mostrar o appWrapper
            } else {
                console.log("User logged in, data already loaded.");
                if (domCache.loadingScreen) domCache.loadingScreen.classList.add('hidden');
                if (domCache.appWrapper) domCache.appWrapper.classList.remove('hidden');
                const currentActiveTab = document.querySelector('#edit-nav .nav-btn.active')?.dataset.tab || 'edicao';
                initializeTabContent(currentActiveTab);
            }

        } else {
            // --- USUÁRIO NÃO ESTÁ LOGADO OU É ANÔNIMO ---
            console.log("Auth state: Logged Out or Anonymous. Access Denied.");
            if (domCache.userEmailEdit) domCache.userEmailEdit.textContent = 'Acesso Negado';

            // Esconde a tela de loading e o app
            if (domCache.loadingScreen) domCache.loadingScreen.classList.add('hidden');
            if (domCache.appWrapper) domCache.appWrapper.classList.add('hidden');

            // Prepara e mostra a tela de "Acesso Negado"
            const authGateMessage = `<div class="flex items-center justify-center h-screen"><div class="text-center p-8 bg-white rounded-lg shadow-xl"><h2 class="text-2xl font-bold text-red-600 mb-4">Acesso Negado</h2><p>Esta página é restrita a usuários com permissão de edição.</p><p class="mt-4 text-sm"><a href="index.html" class="text-blue-600 hover:underline">Voltar para a página principal.</a></p></div></div>`;
            if (domCache.authGate) {
                domCache.authGate.innerHTML = authGateMessage;
                domCache.authGate.classList.remove('hidden');
            }
        }
    });


    // Listeners de Navegação (Lazy Loading)
    if(domCache.navButtons) {
        domCache.navButtons.forEach(button => {
            button.addEventListener('click', (e) => {
                const tabName = e.currentTarget.dataset.tab;
                // Troca visual da aba ativa
                domCache.navButtons.forEach(btn => btn.classList.toggle('active', btn.dataset.tab === tabName));
                // Mostra/Esconde painéis de conteúdo
                domCache.contentPanes.forEach(pane => {
                     const paneId = pane.id || '';
                     pane.classList.toggle('hidden', !paneId.startsWith(`content-${tabName}`));
                });


                // Inicializa o conteúdo da aba SE logado (ADMIN) e dados carregados
                if (auth.currentUser && !auth.currentUser.isAnonymous && dataLoaded) {
                    initializeTabContent(tabName);
                }
                // Não precisa de else, pois se não for admin/logado, o authGate está visível
            });
        });
    }

    // Adiciona listeners para os modais (importante!) - **CORREÇÃO AQUI**
    document.getElementById('desc-choice-cancel-btn')?.addEventListener('click', handleDescChoiceCancel); // Listener movido para ser adicionado após definição
    document.getElementById('desc-choice-keep-btn')?.addEventListener('click', handleDescChoiceKeep);     // Listener movido
    document.getElementById('desc-choice-update-btn')?.addEventListener('click', handleDescChoiceUpdate); // Listener movido


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
            // Usa closest para pegar o botão correto, ou o overlay
            if (e.target.matches('.modal-overlay') || e.target.closest('#desc-choice-cancel-btn')) {
                 handleDescChoiceCancel(); // Usa o handler para limpar seleção
            }
        }

        // Adicionar fechamento para outros modais se necessário,
        // usando seus respectivos botões/overlays e funções de fechamento
    });

    // --- Adiciona listeners que dependem do DOM da Aba Otimizada ---
    const debouncedFilter = debounce(applyFiltersAndPaginate, DEBOUNCE_DELAY);
    domCache.editFilterUnidade?.addEventListener('change', debouncedFilter); // Adicionado listener para Unidade
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
    // MUDANÇA: Redireciona para index.html para que o login possa ser refeito (não há login nesta página)
    document.getElementById('logout-btn')?.addEventListener('click', () => { handleLogout(); window.location.href = 'index.html'; });

    document.getElementById('confirm-delete-edit-btn')?.addEventListener('click', confirmDeleteItems);
    document.getElementById('cancel-delete-edit-btn')?.addEventListener('click', closeDeleteConfirmModal);


}); // Fim do DOMContentLoaded
