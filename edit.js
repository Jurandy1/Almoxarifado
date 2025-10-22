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
            return; // Impede a continuação se houver erro
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
        return; // Já inicializado
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
                 initSobrantesTab(); // Criar esta função
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

        document.getElementById('total-sobrando').textContent = filtered.length;
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

// applyFiltersAndPaginate, renderEditableTable, updatePaginationControls,
// setupEventDelegation, saveAllChanges, goToPage já foram definidas acima
// carregarPadroesConciliacao, calculateSimilarity, levenshteinDistance também

// --- FIM: SEÇÃO ULTRA OTIMIZADA (Funções coladas) ---


// --- SEÇÃO ORIGINAL MANTIDA (Outras Abas) ---

// populateUnitMappingTab, updateSystemUnitOptions, updateGiapUnitOptions,
// renderSavedMappings, populatePendingTransfersTab, parsePtBrDate,
// populateNfTab, renderNfList, populateGiapTab, populateImportAndReplaceTab,
// populateReconciliationTab, renderList, getGlobalLeftovers, getConciliationData,
// handleSelect, updateImportButton, clearGiapImportSelection, addLinkToCreate,
// renderCreatedLinks, renderConciliationLists, openDescriptionChoiceModal,
// closeDescriptionChoiceModal, renderItensATombar, populateSobrantesTab,
// getFilteredSobrantes, renderSobrantesConciliation, findBestMatchForItem,
// renderEditByDescPreview
// ... (Todas as funções originais que NÃO são da aba 'edicao' devem ser mantidas aqui)
// (Cole as funções originais aqui, ajustando nomes se necessário para evitar conflitos)

// Exemplo de como as funções originais são mantidas:
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
    const selectedType = document.getElementById('map-filter-tipo').value;
    const linkedSystemUnits = Object.keys(unitMapping);
    const systemUnits = [...normalizedSystemUnits.values()].filter(unit => {
        const item = fullInventory.find(i => i.Unidade === unit);
        const isCorrectType = !selectedType || item?.Tipo === selectedType;
        return isCorrectType && !linkedSystemUnits.includes(unit);
    }).sort();
    document.getElementById('map-system-unit-select').innerHTML = systemUnits.map(u => `<option value="${escapeHtml(u)}">${escapeHtml(u)}</option>`).join('');
}

function updateGiapUnitOptions() {
    // ... (código original mantido)
    const filterText = normalizeStr(document.getElementById('map-giap-filter').value);
    let allGiapUnitsFromSheet = [...new Set(giapInventory.map(i => i.Unidade).filter(Boolean))];
    let allGiapUnits = [...new Set([...allGiapUnitsFromSheet, ...customGiapUnits.map(u => u.name)])].sort();

    const selectedSystemUnits = Array.from(document.getElementById('map-system-unit-select').selectedOptions).map(opt => opt.value);

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
        unit.split('/').forEach(part => keywords.add(normalizeStr(part.trim())));
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

    document.getElementById('map-giap-unit-multiselect').innerHTML = suggestionHeader + suggestions.join('') + suggestionFooter + available.join('') + usedHeader + usedByOthers.join('') + usedFooter;
}


function renderSavedMappings() {
    // ... (código original mantido)
    const savedMappingsContainer = document.getElementById('saved-mappings-container');
    const mappedUnits = Object.keys(unitMapping).filter(key => unitMapping[key]?.length > 0).sort();
    savedMappingsContainer.innerHTML = mappedUnits.length > 0 ? mappedUnits.map(systemUnit => `
        <div class="p-2 border rounded-md bg-slate-50 flex justify-between items-center">
            <div><strong class="text-sm">${escapeHtml(systemUnit)}</strong><p class="text-xs text-slate-600">→ ${unitMapping[systemUnit].join(', ')}</p></div>
            <button class="delete-mapping-btn text-red-500 hover:text-red-700 p-1" data-system-unit="${escapeHtml(systemUnit)}">
                <svg class="pointer-events-none" xmlns="http://www.w.org/2000/svg" width="16" height="16" fill="currentColor" viewBox="0 0 16 16"><path d="M5.5 5.5A.5.5 0 0 1 6 6v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m2.5 0a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m3 .5a.5.5 0 0 0-1 0v6a.5.5 0 0 0 1 0V6z"/><path fill-rule="evenodd" d="M14.5 3a1 1 0 0 1-1 1H13v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V4h-.5a1 1 0 0 1-1-1V2a1 1 0 0 1 1-1H6a1 1 0 0 1 1-1h2a1 1 0 0 1 1 1h3.5a1 1 0 0 1 1 1v1zM4.118 4 4 4.059V13a1 1 0 0 0 1 1h6a1 1 0 0 0 1-1V4.059L11.882 4H4.118zM2.5 3h11V2h-11v1z"/></svg>
            </button>
        </div>`).join('') : `<p class="text-sm text-slate-500">Nenhuma ligação salva ainda.</p>`;
}

function populatePendingTransfersTab() {
    // ... (código original mantido)
    const pendingTransfersContainer = document.getElementById('pending-transfers-container');
     const pendingTransfers = fullInventory.filter(item => {
        const tombo = item.Tombamento?.trim();
        if (!tombo || normalizeStr(tombo).includes('permuta') || tombo.toLowerCase() === 's/t') return false;

        const giapItem = giapMap.get(tombo);
        if (!giapItem) return false;

        const systemUnit = (item.Unidade || '').trim();
        const giapUnit = giapItem.Unidade;
        if (!systemUnit || !giapUnit) return false;

        if (!unitMapping[systemUnit] || unitMapping[systemUnit].length === 0) {
            return normalizeStr(systemUnit) !== normalizeStr(giapUnit);
        }

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
                    const giapItem = giapMap.get(item.Tombamento.trim());
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
    // ... (código original mantido)
    if (!dateStr || typeof dateStr !== 'string') return new Date(0);
    const parts = dateStr.split('/');
    if (parts.length === 3) {
        return new Date(parts[2], parts[1] - 1, parts[0]);
    }
    const isoParts = dateStr.split('-');
    if(isoParts.length === 3) {
        return new Date(isoParts[0], isoParts[1] - 1, isoParts[2]);
    }
    return new Date(0);
}

function populateNfTab() {
    // ... (código original mantido)
    if (giapInventory.length === 0) return;

    const giapWithNf = giapInventory
        .filter(item => item.NF && item.NF.trim() !== '')
        .sort((a, b) => parsePtBrDate(b.Cadastro) - parsePtBrDate(a.Cadastro));

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

    const allStatuses = [...new Set(giapInventory.map(item => (item.Status || '').trim()).filter(Boolean))].sort();
    const statusFilterEl = document.getElementById('nf-status-filter');
    if (statusFilterEl) {
        statusFilterEl.innerHTML = '<option value="">Todos os Status</option>' + allStatuses.map(s => `<option value="${escapeHtml(s)}">${escapeHtml(s)}</option>`).join('');
    }

    renderNfList();
}

function renderNfList() {
    // ... (código original mantido)
    const container = document.getElementById('notas-fiscais-container');
    container.innerHTML = '';
    const tomboMap = new Map(fullInventory.map(item => [item.Tombamento?.trim(), item]));

    const nfSearchTerm = document.getElementById('nf-search').value.toLowerCase();
    const nfItemSearchTerm = document.getElementById('nf-item-search').value.toLowerCase();
    const nfFornecedorTerm = document.getElementById('nf-fornecedor-search').value.toLowerCase();
    const nfTipoEntrada = document.getElementById('nf-tipo-entrada').value;
    const nfStatusFilter = document.getElementById('nf-status-filter').value;
    const startDateStr = document.getElementById('nf-date-start').value;
    const endDateStr = document.getElementById('nf-date-end').value;

    const startDate = startDateStr ? parsePtBrDate(startDateStr) : null;
    let endDate = endDateStr ? parsePtBrDate(endDateStr) : null;
    if (endDate) { endDate.setDate(endDate.getDate() + 1); }

    const filteredNfs = Object.keys(processedNfData).filter(nf => {
        const nfGroup = processedNfData[nf];
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
        if (endDate && nfDate >= endDate) return false;
        return true;
    });

    if (filteredNfs.length === 0) {
        container.innerHTML = `<p class="text-slate-500 text-center p-4">Nenhuma nota fiscal encontrada com os filtros aplicados.</p>`;
        return;
    }

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
        container.appendChild(categoryHeader);
        categorizedNfs[category].forEach(nf => {
            let totalNfValue = 0;
            const nfGroup = processedNfData[nf];
            const nfDetails = document.createElement('details');
            nfDetails.className = 'bg-white rounded-lg shadow-sm border mb-3 border-t-0 rounded-t-none';
            nfDetails.open = false;

            const itemSummaryText = nfGroup.items.slice(0, 2).map(i => escapeHtml(i.Descrição || i.Espécie)).join(', ') + (nfGroup.items.length > 2 ? '...' : '');

            nfDetails.innerHTML = `
                <summary class="p-4 font-semibold cursor-pointer grid grid-cols-1 md:grid-cols-3 gap-4 items-center hover:bg-slate-50">
                    <div class="md:col-span-2">
                        <p class="text-xs text-slate-500">NF: <strong class="text-blue-700 text-sm">${escapeHtml(nf)}</strong> | Fornecedor: <strong>${escapeHtml(nfGroup.fornecedor)}</strong></p>
                        <p class="text-xs text-slate-500 mt-1 truncate">Itens: ${itemSummaryText}</p>
                    </div>
                    <div><p class="text-xs text-slate-500">Data Cadastro</p><strong>${escapeHtml(nfGroup.dataCadastro)}</strong></div>
                </summary>
            `;

            const itemsListContainer = document.createElement('div');
            itemsListContainer.className = 'p-4 border-t border-slate-200 space-y-2';

            const itemsToDisplay = nfStatusFilter ? nfGroup.items.filter(item => (item.Status || '').trim() === nfStatusFilter) : nfGroup.items;

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

                itemsListContainer.innerHTML += `
                    <div class="p-3 border rounded-md flex justify-between items-start gap-4 ${itemClass}">
                        <div class="flex-1"><p class="font-bold text-slate-800 ${!allocatedItem && !isAvailableForUse ? 'line-through' : ''}">${escapeHtml(item.Descrição || item.Espécie)}</p><p class="text-sm text-slate-500">Tombamento: <span class="font-mono">${escapeHtml(tombo || 'N/D')}</span></p></div>
                        <div class="text-right"><p class="text-xs text-slate-500">Valor</p><p class="font-semibold text-green-700">${parseCurrency(item['Valor NF']).toLocaleString('pt-BR', { style: 'currency', currency: 'BRL' })}</p></div>
                        <div class="text-right ml-4 space-y-1.5 min-w-[150px]">${statusHtml}${allocationHtml}</div>
                    </div>
                `;
            });

            if (itemsToDisplay.length === nfGroup.items.length) {
                itemsListContainer.innerHTML += `<div class="p-3 border-t-2 mt-2 font-bold text-slate-800 flex justify-between items-center"><span>VALOR TOTAL DA NOTA</span><span>${totalNfValue.toLocaleString('pt-BR', { style: 'currency', currency: 'BRL' })}</span></div>`;
            }

            nfDetails.appendChild(itemsListContainer);
            container.appendChild(nfDetails);
        });
    });
}

function populateGiapTab() {
    // ... (código original mantido)
    const giapTableBody = document.getElementById('giap-table-body');
    const headers = ['TOMBAMENTO', 'Descrição', 'Unidade', 'Status', 'Alocação', 'Cadastro', 'NF', 'Nome Fornecedor'];
    const thead = giapTableBody.closest('table').querySelector('thead tr');
    thead.innerHTML = headers.map(h => `<th class="p-3 text-left font-semibold">${h}</th>`).join('');

    const tomboMap = new Map(fullInventory.map(item => [normalizeTombo(item.Tombamento), item]));

    giapTableBody.innerHTML = giapInventory.map(item => {
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
    const tipos = [...new Set(fullInventory.map(item => item.Tipo).filter(Boolean))].sort();

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
            const unidades = [...new Set(fullInventory.filter(i => i.Tipo === selectedTipo).map(i => i.Unidade).filter(Boolean))].sort();
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
    const tipos = [...new Set(fullInventory.map(item => item.Tipo).filter(Boolean))].sort();
    const sel = document.getElementById('filter-tipo');
    sel.innerHTML = '<option value="">Todos os Tipos</option>' + tipos.map(t => `<option value="${t}">${t}</option>`).join('');

    const tombarFilterTipo = document.getElementById('tombar-filter-tipo');
    tombarFilterTipo.innerHTML = '<option value="">Todos os Tipos</option>' + tipos.map(t => `<option value="${t}">${t}</option>`).join('');

    // Garante que o select de unidade comece desabilitado
    const selU = document.getElementById('filter-unidade');
    selU.innerHTML = '<option value="">Selecione um Tipo primeiro</option>';
    selU.disabled = true;
    const selUTombar = document.getElementById('tombar-filter-unidade');
    selUTombar.innerHTML = '<option value="">Selecione um Tipo primeiro</option>';
    selUTombar.disabled = true;
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
        const id = item[keyField];
        const div = document.createElement('div');
        div.className = 'reconciliation-list-item card p-2 text-sm';
        div.dataset.id = id;

        let detailsHtml = '';
        if (containerId.includes('system-list')) {
            detailsHtml = `
                <strong>${escapeHtml(item[primaryLabelField])}</strong>
                <p class="text-xs text-slate-500 mt-1">Fornecedor: ${escapeHtml(item.Fornecedor || 'N/D')} | Estado: <strong>${escapeHtml(item.Estado || 'N/A')}</strong></p>
                <p class="text-xs text-slate-400 mt-1">Obs: ${escapeHtml(item.Observação || 'Nenhuma')}</p>
            `;
        } else { // giap-list ou sobrando-list
             detailsHtml = `
                <div class="flex justify-between items-start">
                    <div class="flex-1">
                        <strong>${escapeHtml(item[keyField])} - ${escapeHtml(item.Descrição || item.Espécie || 'N/A')}</strong>
                        <p class="text-xs text-slate-500 mt-1">Cadastro: <strong>${escapeHtml(item.Cadastro || 'N/D')}</strong> | NF: <strong>${escapeHtml(item['NF'] || 'N/A')}</strong></p>
                        <p class="text-xs text-slate-500 mt-1">Fornecedor: <strong>${escapeHtml(item['Nome Fornecedor'] || 'N/D')}</strong></p>
                    </div>
                    <div class="text-right ml-2"><p class="text-xs text-slate-500">Valor NF</p><strong class="text-sm text-green-700">${parseCurrency(item['Valor NF']).toLocaleString('pt-BR', { style: 'currency', currency: 'BRL' })}</strong></div>
                </div>`;
            if (context === 'sobras') {
                 detailsHtml += `<p class="text-xs text-blue-600 font-semibold mt-1">Unidade GIAP Original: ${escapeHtml(item.Unidade || 'N/A')}</p>`;
            }
        }

        div.innerHTML = detailsHtml;

        if (suggestionInfo && suggestionInfo.suggestions.has(id)) {
            const score = suggestionInfo.suggestions.get(id);
            if (index === 0 && score > 0.7) { div.style.backgroundColor = '#dbeafe'; div.style.borderLeft = '4px solid #3b82f6'; }
            else if (score > 0.5) { div.style.backgroundColor = '#e0f2fe'; div.style.borderLeft = '4px solid #0ea5e9'; }
        }

        div.onclick = (event) => handleSelect(containerId, id, item, event.currentTarget);
        container.append(div);
    });
}

function getGlobalLeftovers() {
    // ... (código original mantido)
    const usedTombamentos = new Set(fullInventory.map(i => normalizeTombo(i.Tombamento)).filter(Boolean));
    linksToCreate.forEach(link => usedTombamentos.add(normalizeTombo(link.giapItem.TOMBAMENTO)));

    return giapInventory.filter(g => {
        const tombo = normalizeTombo(g.TOMBAMENTO);
        return tombo && !tombo.includes('permuta') && !usedTombamentos.has(tombo) && normalizeStr(g.Status).includes(normalizeStr('Disponível'));
    });
}

function getConciliationData() {
    // ... (código original mantido)
    const unidade = document.getElementById('filter-unidade').value.trim();
    if (!unidade) return { systemItems: [], giapItems: [] };

    const systemFilterText = normalizeStr(document.getElementById('system-list-filter').value);
    const giapFilterText = normalizeStr(document.getElementById('giap-list-filter').value);

    const usedTombamentos = new Set(fullInventory.map(i => normalizeTombo(i.Tombamento)).filter(Boolean));
    linksToCreate.forEach(link => usedTombamentos.add(normalizeTombo(link.giapItem.TOMBAMENTO)));

    const mappedGiapUnits = unitMapping[unidade] || [unidade];

    const systemItems = fullInventory.filter(i => {
        const tombo = (i.Tombamento || '').trim().toLowerCase();
        const isPending = linksToCreate.some(l => l.systemItem.id === i.id);
        return !isPending &&
               !i.isPermuta && // <-- EXCLUI PERMUTA
               i.Unidade === unidade &&
               (tombo === '' || tombo === 's/t') &&
               normalizeStr(i.Descrição).includes(systemFilterText);
    });

    const giapItems = giapInventory.filter(g => {
        const tomboTrimmed = normalizeTombo(g.TOMBAMENTO);
        const giapDesc = normalizeStr(g.Descrição || g.Espécie);
        return tomboTrimmed &&
               !usedTombamentos.has(tomboTrimmed) &&
               mappedGiapUnits.map(normalizeStr).includes(normalizeStr(g.Unidade)) &&
               normalizeStr(g.Status).includes(normalizeStr('Disponível')) &&
               giapDesc.includes(giapFilterText);
    });

    return { systemItems, giapItems };
}

function handleSelect(containerId, id, obj, element) {
    // ... (código original mantido)
    if (element.classList.contains('linked')) return;

    const isSobrantesTab = containerId.startsWith('sobras-');
    const systemListId = isSobrantesTab ? '#sobras-system-list' : '#system-list';
    const giapListId = isSobrantesTab ? '#sobras-giap-list' : '#giap-list';

    if (containerId.includes('system-list')) {
        clearGiapImportSelection();
        selSys = { id, obj };
        selGiap = null;

        document.querySelectorAll(`${giapListId} .selected`).forEach(el => el.classList.remove('selected'));
        document.querySelectorAll(`${systemListId} .selected, ${systemListId} .selected-for-import`).forEach(el => el.classList.remove('selected', 'selected-for-import'));
        element.classList.add('selected');

        const giapSourceItems = isSobrantesTab ? getFilteredSobrantes() : getConciliationData().giapItems;
        suggestGiapMatchesComAprendizado(obj, giapSourceItems);

    } else if (containerId.includes('giap-list') && selSys) {
        selGiap = { tomb: id, obj };
        document.querySelectorAll(`${giapListId} .selected, ${giapListId} .selected-for-import`).forEach(el => el.classList.remove('selected', 'selected-for-import'));
        element.classList.add('selected');
        openDescriptionChoiceModal();

    } else if (containerId.includes('giap-list') && !selSys && !isSobrantesTab) { // Import only on unit tab
        element.classList.toggle('selected-for-import');
        const index = giapItemsForImport.findIndex(item => item.TOMBAMENTO === id);
        if (index > -1) {
            giapItemsForImport.splice(index, 1);
        } else {
            giapItemsForImport.push(obj);
        }
        updateImportButton();
    }
}

function updateImportButton() {
    // ... (código original mantido)
    const count = giapItemsForImport.length;
    const btn = document.getElementById('import-giap-btn');
    const countEl = document.getElementById('giap-import-count');
    if(countEl) countEl.textContent = count;
    if(btn) btn.disabled = count === 0;
}

function clearGiapImportSelection() {
    // ... (código original mantido)
    giapItemsForImport = [];
    document.querySelectorAll('#giap-list .selected-for-import').forEach(el => el.classList.remove('selected-for-import'));
    updateImportButton();
}

function addLinkToCreate(useGiapDescription) {
    // ... (código original mantido)
    const link = {
        systemItem: selSys.obj,
        giapItem: selGiap.obj,
        useGiapDescription
    };
    linksToCreate.push(link);

    const activeTab = document.getElementById('subtab-conciliar-sobras').classList.contains('hidden') ? 'unidade' : 'sobras';

    if(activeTab === 'unidade') {
        renderCreatedLinks();
        const systemEl = document.querySelector(`#system-list div[data-id='${selSys.id}']`);
        if (systemEl) systemEl.classList.add('linked');
        const giapEl = document.querySelector(`#giap-list div[data-id='${selGiap.tomb}']`);
        if (giapEl) giapEl.classList.add('linked');
    } else {
        renderCreatedLinks('sobras');
         const systemEl = document.querySelector(`#sobras-system-list div[data-id='${selSys.id}']`);
        if (systemEl) systemEl.classList.add('linked');
         const giapEl = document.querySelector(`#sobras-giap-list div[data-id='${selGiap.tomb}']`);
        if (giapEl) giapEl.classList.add('linked');
    }

    selSys = selGiap = null;
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
    document.getElementById('desc-choice-tombo').textContent = selGiap.tomb;
    document.getElementById('desc-choice-current').textContent = selSys.obj.Descrição;
    document.getElementById('desc-choice-new').textContent = selGiap.obj.Descrição || selGiap.obj.Espécie;

    descChoiceModal.classList.remove('hidden');
}

function closeDescriptionChoiceModal() {
    // ... (código original mantido)
     const descChoiceModal = document.getElementById('desc-choice-modal');
    descChoiceModal.classList.add('hidden');
}

function renderItensATombar() {
    // ... (código original mantido)
    const container = document.getElementById('itens-a-tombar-container');
    const tipo = document.getElementById('tombar-filter-tipo').value;
    const unidade = document.getElementById('tombar-filter-unidade').value;

    const itemsPendentes = fullInventory.filter(item =>
        item.etiquetaPendente === true &&
        (!tipo || item.Tipo === tipo) &&
        (!unidade || item.Unidade === unidade)
    );

    if (itemsPendentes.length === 0) {
        container.innerHTML = '<p class="text-slate-500 text-center p-4">Nenhum item pendente de tombamento com os filtros selecionados.</p>';
        return;
    }

    const groupedByTipo = itemsPendentes.reduce((acc, item) => {
        const tipoKey = item.Tipo || 'Sem Tipo';
        if (!acc[tipoKey]) acc[tipoKey] = [];
        acc[tipoKey].push(item);
        return acc;
    }, {});

    let html = '';
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
                                <thead><tr class="border-b"><th class="p-2 text-left">Descrição</th><th class="p-2 text-left">Novo Tombo</th><th class="p-2 text-left">Ação</th></tr></thead>
                                <tbody>`;

            groupedByUnidade[unidade].forEach(item => {
                html += `<tr class="border-b hover:bg-green-50">
                            <td class="p-2">${escapeHtml(item.Descrição)}</td>
                            <td class="p-2 font-mono">${escapeHtml(item.Tombamento)}</td>
                            <td class="p-2">
                                <button data-id="${item.id}" class="confirmar-tombamento-btn text-xs bg-green-100 text-green-700 px-3 py-1 rounded-md hover:bg-green-200">Confirmar Tombamento</button>
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
    const reconciledTypes = [...new Set(fullInventory.filter(i => reconciledUnits.includes(i.Unidade)).map(i => i.Tipo).filter(Boolean))].sort();
    const sobrasTipoSelect = document.getElementById('sobras-filter-tipo');
    sobrasTipoSelect.innerHTML = '<option value="">Selecione um Tipo</option>' + reconciledTypes.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');

    const sobrasGiapTypeSelect = document.getElementById('sobras-giap-type-filter');
    const allTypes = [...new Set(fullInventory.map(i => i.Tipo).filter(Boolean))].sort();
    sobrasGiapTypeSelect.innerHTML = '<option value="">Todos os Tipos</option>' + allTypes.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join('');

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

     // Garante que o select de unidade comece desabilitado
    const sobrasUnidadeSelectInitial = document.getElementById('sobras-filter-unidade');
    sobrasUnidadeSelectInitial.innerHTML = '<option value="">Selecione um Tipo primeiro</option>';
    sobrasUnidadeSelectInitial.disabled = true;

    document.getElementById('sobras-system-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione Tipo e Unidade e clique em Carregar.</p>`;
    document.getElementById('sobras-giap-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Os tombos sobrando aparecerão aqui após carregar os itens do sistema.</p>`;
}

function getFilteredSobrantes() {
     // ... (código original mantido)
    let allLeftovers = getGlobalLeftovers();
    const giapTypeFilter = document.getElementById('sobras-giap-type-filter').value;
    const giapDescFilter = normalizeStr(document.getElementById('sobras-giap-list-filter').value);

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
     // ... (código original mantido)
    const unidade = document.getElementById('sobras-filter-unidade').value;
    if (!unidade) {
        showNotification('Selecione uma unidade para carregar os itens S/T.', 'warning');
        return;
    }
    linksToCreate = [];
    renderCreatedLinks('sobras');

    const systemFilterText = normalizeStr(document.getElementById('sobras-system-list-filter').value);
    const systemItems = fullInventory.filter(i => {
        const tombo = (i.Tombamento || '').trim().toLowerCase();
        const isPending = linksToCreate.some(l => l.systemItem.id === i.id);
        return !isPending &&
               !i.isPermuta &&
               i.Unidade === unidade &&
               (tombo === '' || tombo === 's/t') &&
               normalizeStr(i.Descrição).includes(systemFilterText);
    });
    renderList('sobras-system-list', systemItems, 'id', 'Descrição', null, 'sobras');
    document.getElementById('sobras-quick-actions').classList.remove('hidden');

    const filteredSobrantes = getFilteredSobrantes();
    renderList('sobras-giap-list', filteredSobrantes, 'TOMBAMENTO', 'Descrição', null, 'sobras');
}

function findBestMatchForItem(pastedItem, availableSystemItems) {
    // ... (código original mantido)
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

function renderEditByDescPreview(updates) {
    // ... (código original mantido)
     const container = document.getElementById('edit-by-desc-preview-table-container');
     if (!container) return; // Adiciona verificação
    const existingTombos = new Map(fullInventory.map(i => [normalizeTombo(i.Tombamento), i]));
    document.getElementById('edit-by-desc-preview-count').textContent = updates.length;
    let tableHtml = `<table class="w-full text-xs text-left">
                        <thead class="bg-slate-200">
                            <tr>
                                <th class="p-2 w-1/3">Descrição (Sistema vs. Planilha)</th>
                                <th class="p-2">Dados Atuais no Sistema</th>
                                <th class="p-2">Novos Dados da Planilha</th>
                                <th class="p-2">Status da Correspondência</th>
                            </tr>
                        </thead><tbody>`;
    updates.forEach(upd => {
        let rowClass = '';
        let statusHtml = '';

        switch(upd.status) {
            case 'not_found':
                rowClass = 'bg-yellow-100';
                statusHtml = `<span class="font-bold text-yellow-700">${upd.matchType}</span>`;
                break;
            case 'multiple_found':
                rowClass = 'bg-yellow-100';
                statusHtml = `<span class="font-bold text-yellow-700">${upd.matchType}</span>`;
                break;
            case 'tombo_in_use':
                rowClass = 'bg-red-100';
                statusHtml = `<span class="font-bold text-red-700">Tombo já existe em:<br>${escapeHtml(existingTombos.get(upd.pastedData.tombamento)?.Unidade)}</span>`;
                break;
             case 'tombo_wrong_location':
                rowClass = 'bg-orange-100';
                statusHtml = `<span class="font-bold text-orange-700">Tombo em Local Errado</span><br>GIAP aponta para: <br><strong>${escapeHtml(upd.giapItem?.Unidade || 'N/A')}</strong>`;
                break;
            case 'ok':
                if (upd.matchType.includes('Perfeita') || upd.matchType.includes('Exata')) {
                    statusHtml = `<span class="font-bold text-green-700">${upd.matchType}</span>`;
                } else {
                    statusHtml = `<span class="font-bold text-blue-700">${upd.matchType}</span>`;
                }

                if(!upd.giapItem && upd.pastedData.tombamento && upd.pastedData.tombamento !== 'S/T') {
                    statusHtml += '<br><span class="text-orange-600">Aviso: Tombo não localizado no GIAP.</span>';
                }
                break;
        }

        let descHtml = upd.systemItem ? `<strong>Sistema:</strong> ${escapeHtml(upd.systemItem.Descrição)}` : `<strong>Planilha:</strong> ${escapeHtml(upd.pastedData.descricao)}`;
         if (upd.systemItem && upd.systemItem.Descrição !== upd.pastedData.descricao) {
            descHtml += `<br><strong>Planilha:</strong> <span class="text-blue-600">${escapeHtml(upd.pastedData.descricao)}</span>`
        }

        if (upd.giapItem && upd.systemItem) {
            const giapDesc = upd.giapItem.Descrição || upd.giapItem.Espécie;
            if (giapDesc && upd.systemItem.Descrição.trim() !== giapDesc.trim()) {
                descHtml += `<div class="mt-1 p-1 bg-blue-50 rounded">
                                <label class="inline-flex items-center">
                                    <input type="checkbox" class="h-4 w-4 rounded border-gray-300 use-giap-desc-cb" data-update-id="${upd.id}">
                                    <span class="ml-2 text-blue-800 text-xs">Usar descrição do GIAP: ${escapeHtml(giapDesc)}</span>
                                </label>
                            </div>`;
            }
        }

        const originalData = upd.systemItem ? `T: ${upd.systemItem.Tombamento || 'S/T'}<br>L: ${upd.systemItem.Localização}<br>E: ${upd.systemItem.Estado}` : 'N/A';
        const newData = `<strong>T: ${upd.pastedData.tombamento}</strong><br>L: ${upd.pastedData.localizacao}<br>E: ${upd.pastedData.estado}`;

        tableHtml += `<tr class="${rowClass} border-b">
                        <td class="p-2">${descHtml}</td>
                        <td class="p-2">${originalData}</td>
                        <td class="p-2">${newData}</td>
                        <td class="p-2">${statusHtml}</td>
                      </tr>`;
    });

    container.innerHTML = tableHtml + '</tbody></table>';
}

// --- FIM: SEÇÃO ORIGINAL MANTIDA ---

// --- HANDLERS DE EVENTOS (Separados para organização) ---

// Handlers da Aba Otimizada (já existem na seção otimizada)
// - applyFiltersAndPaginate, saveAllChanges, goToPage, confirmDeleteItems

// Handlers da Aba Ligar Unidades
async function handleSaveMapping() {
    const systemUnits = Array.from(document.getElementById('map-system-unit-select').selectedOptions).map(opt => opt.value.trim());
    if (systemUnits.length === 0) return showNotification("Selecione uma ou mais Unidades do Sistema.", "warning");
    const giapUnits = Array.from(document.getElementById('map-giap-unit-multiselect').selectedOptions).map(opt => opt.value);
    systemUnits.forEach(systemUnit => { unitMapping[systemUnit] = giapUnits; });
    try {
        domCache.feedbackStatus.innerHTML = `<div class="saving-spinner inline-block mr-2"></div> Salvando...`;
        await setDoc(doc(db, 'config', 'unitMapping'), { mappings: unitMapping });
        showNotification('Mapeamento salvo!', 'success');
        domCache.feedbackStatus.textContent = `Mapeamento salvo!`;
        populateUnitMappingTab(); // Re-renderiza a lista de mapeamentos salvos
    } catch (error) { showNotification(`Erro ao salvar.`, 'error'); console.error(error); domCache.feedbackStatus.textContent = `Erro ao salvar.`; }
}

async function handleDeleteMapping(e) {
    const deleteBtn = e.target.closest('.delete-mapping-btn');
    if (deleteBtn) {
        const systemUnit = (deleteBtn.dataset.systemUnit || '').trim();
        delete unitMapping[systemUnit];
        try {
            domCache.feedbackStatus.innerHTML = `<div class="saving-spinner inline-block mr-2"></div> Removendo...`;
            await setDoc(doc(db, 'config', 'unitMapping'), { mappings: unitMapping });
            showNotification(`Ligação removida.`, 'success');
            domCache.feedbackStatus.textContent = `Ligação removida.`;
            populateUnitMappingTab(); // Re-renderiza a lista
        } catch (error) { showNotification(`Erro ao remover.`, 'error'); console.error(error); domCache.feedbackStatus.textContent = `Erro ao remover.`; }
    }
}

// Handlers da Aba Conciliar
function handleConciliationTypeChange() {
    const tipo = document.getElementById('filter-tipo').value;
    const unidades = [...new Set(fullInventory
        .filter(i => !reconciledUnits.includes(i.Unidade))
        .filter(i => !tipo || i.Tipo === tipo)
        .map(i => i.Unidade).filter(Boolean))].sort();
    const selU = document.getElementById('filter-unidade');
    selU.innerHTML = '<option value="">Selecione uma Unidade</option>' + unidades.map(u => `<option>${u}</option>`).join('');
    selU.disabled = false;
}

function handleLoadConciliation() {
    const unidade = document.getElementById('filter-unidade').value.trim();
    const tipo = document.getElementById('filter-tipo').value;
    const warningDiv = document.getElementById('unit-reconciled-warning');

    if (!unidade) {
        if(warningDiv) warningDiv.classList.add('hidden');
        return showNotification('Por favor, selecione uma unidade para carregar.', 'warning');
    }

    if(warningDiv) {
        if(reconciledUnits.includes(unidade)) {
            warningDiv.textContent = `Aviso: Esta unidade já foi finalizada. Para continuar a conciliá-la, vá para a aba "Conciliar com Sobras".`;
            warningDiv.classList.remove('hidden');
        } else {
            warningDiv.classList.add('hidden');
        }
    }

    activeConciliationUnit = unidade;
    activeConciliationType = tipo;

    const unitNameEl = document.getElementById('giap-list-unit-name');
    if(unitNameEl) unitNameEl.textContent = unidade;
    const mappedGiapUnits = unitMapping[unidade] || [unidade];
    if(mappedGiapUnits.length === 1 && mappedGiapUnits[0] === unidade && !unitMapping[unidade]) {
        showNotification('Esta unidade não está mapeada. Vá para a aba "Ligar Unidades".', 'warning');
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
    if(document.getElementById('filter-unidade').value) {
         const { giapItems } = getConciliationData();
         renderList('giap-list', giapItems, 'TOMBAMENTO', 'Descrição');
    }
}

function handleSaveLinksResult(success) {
    if (success) {
        showNotification('Vínculos salvos! Atualizando listas...', 'success');
        renderConciliationLists();
        hideOverlay();
    }
    // O erro já é tratado dentro de savePendingLinks
}

async function handleFinishReconciliation() {
    const unidade = document.getElementById('filter-unidade').value.trim();
    const success = await savePendingLinks('unidade');
    if (success) {
        showOverlay('Finalizando unidade...');
        if (unidade && !reconciledUnits.includes(unidade)) {
            reconciledUnits.push(unidade);
            try {
                await setDoc(doc(db, 'config', 'reconciledUnits'), { units: reconciledUnits });
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
        populateSobrantesTab();
        hideOverlay();
        showNotification('Pronto para conciliar com os itens sobrando.', 'info');
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
     if (giapItemsForImport.length === 0) return showNotification('Nenhum item GIAP selecionado para importar.', 'warning');

    const tipo = activeConciliationType;
    const unidade = activeConciliationUnit;
    if (!unidade || !tipo) return showNotification('Por favor, carregue uma unidade primeiro antes de importar.', 'warning');

    const estado = document.getElementById('import-estado-select').value;

    showOverlay(`Importando ${giapItemsForImport.length} itens...`);
    const batch = writeBatch(db);
    const newItemsForCache = [];

    giapItemsForImport.forEach(giapItem => {
        const newItemRef = doc(collection(db, 'patrimonio')); // Gera ID localmente
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
             populateSobrantesTab(); // Repopula filtros caso dados tenham mudado
         }
         // Limpa listas ao trocar PARA esta aba
         document.getElementById('sobras-system-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione Tipo e Unidade e clique em Carregar.</p>`;
         document.getElementById('sobras-giap-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Os tombos sobrando aparecerão aqui após carregar os itens do sistema.</p>`;
         document.getElementById('sobras-created-links').innerHTML = '';
         document.getElementById('sobras-quick-actions').classList.add('hidden');
    } else { // unidade
         if (!initializedTabs.has('conciliacao_unidade')) {
             // A aba unidade já é populada pelo initReconciliationTab principal
             initializedTabs.add('conciliacao_unidade');
         }
         // Limpa listas ao trocar PARA esta aba
         document.getElementById('system-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione uma unidade e clique em carregar.</p>`;
         document.getElementById('giap-list').innerHTML = `<p class="p-4 text-slate-500 text-center">Selecione uma unidade e clique em carregar.</p>`;
         document.getElementById('created-links').innerHTML = '';
         document.getElementById('quick-actions').classList.add('hidden');
    }
}

// Handlers da Aba Conciliar Sobras
function handleSaveLinksResultSobras(success) {
     if (success) {
        showNotification('Vínculos salvos! Atualizando listas...', 'success');
        renderSobrantesConciliation();
        hideOverlay();
    }
}
function handleClearSobrantesSelections() {
     selSys = selGiap = null;
    document.querySelectorAll('#sobras-system-list .selected').forEach(el => el.classList.remove('selected'));
    document.querySelectorAll('#sobras-giap-list .selected').forEach(el => el.classList.remove('selected'));
    showNotification('Seleções limpas.', 'info');
     // Re-renderiza a lista GIAP sem sugestões
     const filteredSobrantes = getFilteredSobrantes();
     renderList('sobras-giap-list', filteredSobrantes, 'TOMBAMENTO', 'Descrição', null, 'sobras');
}
function handleDeleteCreatedLinkSobras(e) {
    const deleteBtn = e.target.closest('.delete-link-btn');
    if (!deleteBtn) return;
    const index = parseInt(deleteBtn.dataset.index, 10);
    const removedLink = linksToCreate.splice(index, 1)[0];
    if (removedLink) {
        const systemEl = document.querySelector(`#sobras-system-list div[data-id='${removedLink.systemItem.id}']`);
        if (systemEl) systemEl.classList.remove('linked');
        const giapEl = document.querySelector(`#sobras-giap-list div[data-id='${removedLink.giapItem.TOMBAMENTO}']`);
        if (giapEl) giapEl.classList.remove('linked');
    }
    renderCreatedLinks('sobras');
    showNotification('Vínculo removido.', 'info');
}

// Handlers da Aba Itens a Tombar
function handleTombarFilterChange() {
    const tipo = document.getElementById('tombar-filter-tipo').value;
    const unidades = [...new Set(fullInventory
        .filter(i => i.etiquetaPendente === true && (!tipo || i.Tipo === tipo))
        .map(i => i.Unidade).filter(Boolean))].sort();
    const selU = document.getElementById('tombar-filter-unidade');
    selU.innerHTML = '<option value="">Todas as Unidades</option>' + unidades.map(u => `<option>${u}</option>`).join('');
    selU.disabled = false;
    renderItensATombar();
}

async function handleConfirmTombamento(e) {
    const btn = e.target.closest('.confirmar-tombamento-btn');
    if (!btn) return;
    const id = btn.dataset.id;
    btn.disabled = true;
    btn.textContent = 'Salvando...';
    try {
        const docRef = doc(db, 'patrimonio', id);
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
            const docRef = doc(db, 'patrimonio', cb.dataset.id);
            const updateData = { Observação: 'Transferência GIAP ignorada manualmente.', updatedAt: serverTimestamp() };
            batch.update(docRef, updateData);
            itemsToUpdateLocally.push({ id: cb.dataset.id, changes: { Observação: 'Transferência GIAP ignorada manualmente.' } });
        });
    } else if (actionButton.classList.contains('transfer-selected-btn')) {
        actionDescription = `Transferindo ${selectedCheckboxes.length} iten(s)...`;
        selectedCheckboxes.forEach(cb => {
            const docRef = doc(db, 'patrimonio', cb.dataset.id);
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
            itemsToReplace = results.data.map(row => ({
                UNIDADE_EXCEL: (row[0] || '').trim(),
                ITEM: (row[1] || '').trim(),
                TOMBO: (row[2] || '').trim(),
                LOCAL: (row[3] || '').trim(),
                ESTADO: (row[4] || '').trim()
            }));

            const previewList = document.getElementById('replace-preview-list');
            document.getElementById('replace-preview-count').textContent = itemsToReplace.length;
            previewList.innerHTML = itemsToReplace.map(item => `
                <div class="p-2 border-b text-xs">
                    <strong>${escapeHtml(item.ITEM)}</strong> (Tombo: ${escapeHtml(item.TOMBO) || 'S/T'})<br>
                    Local: ${escapeHtml(item.LOCAL)} | Estado: ${escapeHtml(item.ESTADO)}
                </div>
            `).join('');
            document.getElementById('replace-results').classList.remove('hidden');
            // Reseta e desabilita botão de confirmação
            document.getElementById('replace-confirm-checkbox').checked = false;
            document.getElementById('confirm-replace-btn').disabled = true;
        },
        error: (err) => {
            showNotification('Erro ao processar os dados. Verifique o formato.', 'error');
            console.error(err);
             document.getElementById('replace-results').classList.add('hidden');
        }
    });
}

function handleReplaceConfirmChange(e) {
     document.getElementById('confirm-replace-btn').disabled = !e.target.checked;
}

async function handleConfirmReplace() {
    const tipo = document.getElementById('replace-tipo').value;
    const unidade = document.getElementById('replace-unit').value.trim();

    if (!unidade || itemsToReplace.length === 0) return showNotification('Dados inválidos ou unidade não selecionada.', 'error');

    showOverlay(`Substituindo inventário de ${unidade}...`);
    const itemsToDelete = fullInventory.filter(item => item.Unidade.trim() === unidade);
    const idsToDelete = itemsToDelete.map(item => item.id);

    const batch = writeBatch(db);

    itemsToDelete.forEach(item => {
        const docRef = doc(db, 'patrimonio', item.id);
        batch.delete(docRef);
    });

    const newItemsAdded = []; // Para atualizar cache e array
    itemsToReplace.forEach(item => {
        const newItemRef = doc(collection(db, 'patrimonio'));
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
        initializeTabContent('edicao'); // Repopula filtros da aba principal
        populateUnitMappingTab();
        populateReconciliationTab();
        populatePendingTransfersTab();

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
            const inventoryInUnit = fullInventory.filter(i => i.Unidade === unidade);
            const existingTombos = new Map(fullInventory.map(i => [normalizeTombo(i.Tombamento), i]));

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
            document.getElementById('edit-by-desc-results').classList.remove('hidden');
            const validCount = updatesToProcess.filter(u => u.status === 'ok' || u.status === 'tombo_not_in_giap').length;
            document.getElementById('confirm-edit-by-desc-btn').disabled = validCount === 0;
            document.getElementById('edit-by-desc-preview-count').textContent = `${updatesToProcess.length} (Válidos para salvar: ${validCount})`;

        },
         error: (err) => {
            showNotification('Erro ao processar dados. Verifique formato e cabeçalhos.', 'error');
            console.error(err);
             document.getElementById('edit-by-desc-results').classList.add('hidden');
        }
    });
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
    const validUpdates = updatesToProcess.filter(u => u.status === 'ok' || u.status === 'tombo_not_in_giap'); // Inclui tombo_not_in_giap
    if(validUpdates.length === 0) return showNotification('Nenhum item válido para atualizar.', 'error');

    showOverlay(`Atualizando ${validUpdates.length} itens...`);
    const batch = writeBatch(db);
    const itemsToUpdateLocally = [];

    validUpdates.forEach(upd => {
        const docRef = doc(db, 'patrimonio', upd.systemItem.id);
        const updatePayload = {
            // Tombamento SÓ é atualizado se for válido (existe no GIAP ou é S/T)
            ...(upd.status !== 'tombo_not_in_giap' && { Tombamento: upd.pastedData.tombamento }),
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
        if(upd.status !== 'tombo_not_in_giap' && upd.pastedData.tombamento && upd.pastedData.tombamento.toLowerCase() !== 's/t') {
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
                 fullInventory[index] = { ...fullInventory[index], ...update.changes };
             }
        });

        showNotification(`${validUpdates.length} itens atualizados com sucesso! Atualizando visualização...`, 'success');
        // Limpa a UI da aba
        document.getElementById('edit-by-desc-data').value = '';
        document.getElementById('edit-by-desc-results').classList.add('hidden');
        updatesToProcess = [];
         // Repopula selects em outras abas que podem ter sido afetadas
        initializeTabContent('edicao'); // Repopula filtros da aba principal
        populateUnitMappingTab();
        populateReconciliationTab();
        populatePendingTransfersTab();

    } catch(e) {
        showNotification('Erro ao atualizar os itens.', 'error');
        console.error(e);
    } finally {
         hideOverlay();
    }
}

function handleMassTransferSearch() {
    const tombosInput = document.getElementById('mass-transfer-tombos').value;
    const tombos = tombosInput.split(/[\s,]+/).map(t => normalizeTombo(t.trim())).filter(Boolean); // Normaliza aqui
    const existingTombos = new Set(fullInventory.map(i => normalizeTombo(i.Tombamento))); // Normaliza aqui
    const foundItems = []; const notFound = [];
    tombos.forEach(tombo => {
        const giapItem = giapMap.get(tombo); // Já busca normalizado
        if (giapItem && !existingTombos.has(tombo)) foundItems.push(giapItem);
        else notFound.push(tombo);
    });
    if (notFound.length > 0) showNotification(`Não encontrados ou já existem: ${notFound.join(', ')}`, 'warning', 5000);
    const massTransferResults = document.getElementById('mass-transfer-results');
    if (foundItems.length > 0) {
        const massTransferList = document.getElementById('mass-transfer-list');
        const estadoOptions = ['Novo', 'Bom', 'Regular', 'Avariado'];
        massTransferList.innerHTML = foundItems.map(item => `
            <div class="p-2 border rounded-md bg-slate-50 grid grid-cols-3 gap-4 items-center">
                <div class="col-span-2"><strong>${escapeHtml(item.TOMBAMENTO)}</strong> - ${escapeHtml(item.Descrição || item.Espécie)}</div>
                <div><select data-tombo="${escapeHtml(item.TOMBAMENTO)}" class="mass-transfer-status w-full p-1 border rounded bg-white">${estadoOptions.map(opt => `<option>${opt}</option>`).join('')}</select></div>
            </div>`).join('');
        massTransferResults.classList.remove('hidden');
    } else {
        massTransferResults.classList.add('hidden');
    }
}

function handleMassTransferSetAllStatus(e) {
    document.querySelectorAll('.mass-transfer-status').forEach(select => select.value = e.target.value);
}

async function handleMassTransferConfirm() {
    const massTransferUnitEl = document.getElementById('mass-transfer-unit');
    const massTransferTipoEl = document.getElementById('mass-transfer-tipo');
    const destinationUnit = massTransferUnitEl.value;
    const destinationTipo = massTransferTipoEl.value;
    if (!destinationUnit) return showNotification('Selecione uma unidade de destino.', 'warning');
    if (!destinationTipo) return showNotification('Selecione um tipo de unidade de destino.', 'warning');

    const itemsToCreate = Array.from(document.querySelectorAll('.mass-transfer-status'));
    if (itemsToCreate.length === 0) return;

    showOverlay(`Criando ${itemsToCreate.length} itens...`);
    const batch = writeBatch(db);
    const newItemsForCache = []; // Para atualizar localmente

    itemsToCreate.forEach(select => {
        const tombo = select.dataset.tombo;
        const giapItem = giapMap.get(tombo); // Busca normalizado
        if (giapItem) {
            const newItemRef = doc(collection(db, 'patrimonio'));
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

        showNotification(`${itemsToCreate.length} itens criados com sucesso! Atualizando...`, 'success');
         // Limpa a UI da aba
        document.getElementById('mass-transfer-tombos').value = '';
        document.getElementById('mass-transfer-results').classList.add('hidden');
        document.getElementById('mass-transfer-list').innerHTML = '';
         // Repopula selects em outras abas que podem ter sido afetadas
        initializeTabContent('edicao'); // Repopula filtros da aba principal
        populateUnitMappingTab();
        populateReconciliationTab();
        populatePendingTransfersTab();

    } catch (e) {
        showNotification('Erro ao criar itens em massa.', 'error');
        console.error(e);
    } finally {
        hideOverlay();
    }
}

async function handleSaveGiapUnit() {
    const newUnitName = document.getElementById('add-giap-name').value.trim();
    const newUnitNumber = document.getElementById('add-giap-number').value.trim();
    if (!newUnitName) {
        return showNotification('O nome da unidade não pode ser vazio.', 'warning');
    }

    const normalizedNewName = normalizeStr(newUnitName);
    const allGiapUnitNames = new Set(giapInventory.map(i => normalizeStr(i.Unidade)).filter(Boolean));
    const allCustomUnitNames = new Set(customGiapUnits.map(u => normalizeStr(u.name)));

    if (allGiapUnitNames.has(normalizedNewName) || allCustomUnitNames.has(normalizedNewName)) {
        return showNotification('Esta unidade já existe.', 'error');
    }

    showOverlay('Salvando nova unidade...');
    const updatedCustomUnits = [...customGiapUnits, { name: newUnitName, number: newUnitNumber }];

    try {
        const docRef = doc(db, 'config', 'customGiapUnits');
        await setDoc(docRef, { units: updatedCustomUnits });
        customGiapUnits.push({ name: newUnitName, number: newUnitNumber });
        showNotification('Nova unidade salva com sucesso!', 'success');
        document.getElementById('add-giap-name').value = '';
        document.getElementById('add-giap-number').value = '';
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

// Handlers do Modal Descrição
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

// --- FIM DOS HANDLERS ---


// --- INICIALIZAÇÃO GERAL ---
document.addEventListener('DOMContentLoaded', () => {
    initDomElements(); // Cache DOM elements first

    // Adiciona listener de autenticação APRIMORADO
    addAuthListener(user => {
        if (!authReady) {
            // Este é o primeiro callback, define o estado inicial
            authReady = true;
            console.log("Auth state initialized.");
        }

        if (user) {
            domCache.userEmailEdit.textContent = user.email;
            domCache.authGate.classList.add('hidden'); // Esconde o bloqueio
            domCache.loadingScreen.classList.remove('hidden'); // Mostra carregando dados
             domCache.feedbackStatus.textContent = "Usuário autenticado. Carregando dados...";
            if (!dataLoaded) {
                 loadData(false); // Carrega os dados APENAS se logado e dados não carregados
            } else {
                 domCache.loadingScreen.classList.add('hidden'); // Esconde o loading se dados já estavam carregados
            }
        } else {
            domCache.userEmailEdit.textContent = 'Não logado';
            domCache.authGate.classList.remove('hidden'); // Mostra o bloqueio
            domCache.loadingScreen.classList.add('hidden'); // Esconde o carregando
             domCache.loadingScreen.innerHTML = `<div class="text-center"><h2 class="text-2xl font-bold text-red-600">Acesso Negado</h2><p>Você precisa estar logado para acessar esta página. Volte para a página principal para fazer o login.</p></div>`; // Mensagem de erro no loading screen
        }
    });

    // Listeners de Navegação (Lazy Loading)
    domCache.navButtons.forEach(button => {
        button.addEventListener('click', (e) => {
            const tabName = e.currentTarget.dataset.tab;
            // Troca visual da aba ativa
            domCache.navButtons.forEach(btn => btn.classList.toggle('active', btn.dataset.tab === tabName));
            // Mostra/Esconde painéis de conteúdo
            domCache.contentPanes.forEach(pane => pane.classList.toggle('hidden', !pane.id.endsWith(`-${tabName}`))); // Ajusta para ID correto

            // Inicializa o conteúdo da aba SE necessário
            if (authReady && auth.currentUser && dataLoaded) {
                initializeTabContent(tabName);
            } else if (authReady && !auth.currentUser) {
                 console.log("User not logged in, cannot initialize tab content.");
            } else {
                 console.log("Auth or data not ready, delaying tab initialization.");
            }
        });
    });

    // Adiciona listeners para os modais (importante!)
    document.getElementById('desc-choice-cancel-btn')?.addEventListener('click', handleDescChoiceCancel);
    document.getElementById('desc-choice-keep-btn')?.addEventListener('click', handleDescChoiceKeep);
    document.getElementById('desc-choice-update-btn')?.addEventListener('click', handleDescChoiceUpdate);

    // Adiciona listener para fechar modais genéricos
    document.addEventListener('click', (e) => {
        if (e.target.matches('.modal-overlay') || e.target.closest('.js-close-modal-delete')) {
            closeDeleteConfirmModal();
        }
         if (e.target.matches('.modal-overlay') || e.target.closest('.js-close-modal-add')) {
             // A função closeAddItemModal não foi definida, precisa adicioná-la se o modal ainda existir
             // closeAddItemModal();
         }
         // Adicionar fechamento para outros modais se necessário
    });

}); // Fim do DOMContentLoaded

