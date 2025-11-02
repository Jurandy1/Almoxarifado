/**
 * index.js
 * Este arquivo controla toda a interatividade da página principal (index.html).
 * Funções:
 * - Carregar e exibir os dados no dashboard e na tabela de patrimônio.
 * - Gerenciar filtros, busca e paginação.
 * - Controlar a exibição de modais para login, adição, edição e exclusão de itens.
 */

// Importações do módulo compartilhado
import { db, auth, idb, CACHE_DURATION_MS, GIAP_SHEET_URL, loadFirebaseInventory, loadGiapInventory } from './shared.js';
import { addAuthListener, handleLogin, handleLogout } from './shared.js';
import { showNotification, normalizeStr, debounce, escapeHtml } from './shared.js';
// Importações de bibliotecas do Firebase
import { collection, addDoc, doc, updateDoc, deleteDoc, serverTimestamp, getDocs, query, orderBy, limit } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";

// --- ESTADO DA APLICAÇÃO ---
let patrimonioFullList = [], historicoFullList = [], giapInventory = [];
let processedNfData = {};
let isLoggedIn = false;
let dashboardEstadoChart, dashboardTipoChart;
let patrimonioFilteredList = [], patrimonioCurrentPage = 1;
const patrimonioItemsPerPage = 25;

// --- ELEMENTOS DO DOM ---
const statusFeedbackEl = document.getElementById('status-feedback');
const tableBodyEl = document.getElementById('inventory-table-body');
const paginationControlsEl = document.getElementById('pagination-controls');
const paginationSummaryEl = document.getElementById('pagination-summary');
const filtroTipoUnidadeEl = document.getElementById('filtro-tipo-unidade');
const filtroUnidadeEl = document.getElementById('filtro-unidade');
const filtroEstadoEl = document.getElementById('filtro-estado');
const filtroBuscaEl = document.getElementById('filtro-busca');
const resetFiltersBtn = document.getElementById('reset-filters-btn');
const itemModal = document.getElementById('item-modal');
const openAddModalBtn = document.getElementById('open-add-modal-btn');
const itemForm = document.getElementById('item-form');
const loginModal = document.getElementById('login-modal');
const openLoginModalBtn = document.getElementById('open-login-modal-btn');
const loginForm = document.getElementById('login-form');
const transferModal = document.getElementById('transfer-modal');
const transferForm = document.getElementById('transfer-form');
const userInfoEl = document.getElementById('user-info');
const userEmailEl = document.getElementById('user-email');
const logoutBtn = document.getElementById('logout-btn');
const adminActionsPatrimonio = document.getElementById('admin-actions-patrimonio');
const deleteConfirmModal = document.getElementById('delete-confirm-modal');
const confirmDeleteBtn = document.getElementById('confirm-delete-btn');
const navButtons = document.querySelectorAll('#main-nav > .nav-btn, #main-nav > a.nav-btn');
const contentPanes = document.querySelectorAll('main > .tab-content');
const historyContainer = document.getElementById('history-container');

// --- CARREGAMENTO DE DADOS ---
async function loadAllData(forceRefresh = false) {
    tableBodyEl.innerHTML = `<tr><td colspan="7" class="text-center p-10"><div class="loading-spinner"></div><p class="mt-4">Carregando dados...</p></td></tr>`;
    
    const metadata = await idb.metadata.get('lastFetch');
    const isCacheStale = !metadata || (Date.now() - metadata.timestamp > CACHE_DURATION_MS);

    if (!forceRefresh && !isCacheStale) {
        statusFeedbackEl.textContent = 'Carregando dados do cache local...';
        [patrimonioFullList, giapInventory] = await Promise.all([
            idb.patrimonio.toArray(),
            idb.giap.toArray()
        ]);
        showNotification('Dados carregados do cache.', 'info');
    } else {
        statusFeedbackEl.textContent = 'Buscando dados atualizados do servidor...';
        try {
            const [freshPatrimonio, freshGiapData] = await Promise.all([
                loadFirebaseInventory(),
                loadGiapInventory()
            ]);
            
            freshPatrimonio.sort((a, b) => (a.Descrição || '').localeCompare(b.Descrição || ''));
            
            patrimonioFullList = freshPatrimonio;
            giapInventory = freshGiapData;

            await idb.transaction('rw', idb.patrimonio, idb.giap, idb.metadata, async () => {
                await idb.patrimonio.clear();
                await idb.giap.clear();
                await idb.patrimonio.bulkAdd(patrimonioFullList);
                await idb.giap.bulkAdd(giapInventory);
                await idb.metadata.put({ key: 'lastFetch', timestamp: Date.now() });
            });
            showNotification('Dados atualizados com sucesso!', 'success');
        } catch (error) {
             console.error("Erro ao carregar dados: ", error);
             statusFeedbackEl.textContent = 'Erro ao carregar dados.';
             showNotification('Falha ao carregar dados do servidor.', 'error');
             [patrimonioFullList, giapInventory] = await Promise.all([
                idb.patrimonio.toArray(),
                idb.giap.toArray()
             ]);
        }
    }
    statusFeedbackEl.textContent = `Pronto. ${patrimonioFullList.length} itens carregados.`;
    initializeUI();
}

async function loadHistory() {
    if(!isLoggedIn) return;
    try {
        const q = query(collection(db, "historico"), orderBy("timestamp", "desc"), limit(100));
        const querySnapshot = await getDocs(q);
        historicoFullList = querySnapshot.docs.map(doc => ({id: doc.id, ...doc.data()}));
        renderHistory();
    } catch(e){
        console.error("Error loading history: ", e);
    }
}

// --- INICIALIZAÇÃO E RENDERIZAÇÃO DA UI ---

function initializeUI() {
    populateFilters(patrimonioFullList);
    applyPatrimonioFiltersAndRender();
    if (document.getElementById('content-dashboard').offsetParent) {
         renderDashboard(patrimonioFullList);
    }
    if (isLoggedIn) {
        document.getElementById('tab-notas').style.display = 'inline-block';
        populateNfTab();
    }
}

function updateUIVisibility() {
    const loggedInElements = [adminActionsPatrimonio, document.getElementById('table-header-actions'), document.getElementById('nav-edit-link'), document.getElementById('nav-history')];
    
    if (isLoggedIn) {
        userEmailEl.textContent = auth.currentUser.email;
        userInfoEl.classList.remove('hidden'); userInfoEl.classList.add('flex');
        openLoginModalBtn.classList.add('hidden');
        loggedInElements.forEach(el => el && el.classList.remove('hidden'));
    } else {
        userEmailEl.textContent = '';
        userInfoEl.classList.add('hidden'); userInfoEl.classList.remove('flex');
        openLoginModalBtn.classList.remove('hidden');
        loggedInElements.forEach(el => el && el.classList.add('hidden'));
    }
    document.querySelectorAll('.modal').forEach(m => m.classList.add('hidden'));
    applyPatrimonioFiltersAndRender();
}

// --- LÓGICA DA ABA PATRIMÔNIO ---

function populateFilters(items) {
    const tipos = [...new Set(items.map(item => item.Tipo).filter(Boolean))].sort();
    filtroTipoUnidadeEl.innerHTML = '<option value="">TODOS OS TIPOS</option>' + tipos.map(t => `<option value="${t}">${t}</option>`).join('');
    const estados = ['Novo', 'Bom', 'Regular', 'Avariado'];
    filtroEstadoEl.innerHTML = '<option value="">TODOS OS ESTADOS</option>' + estados.map(e => `<option value="${e}">${e}</option>`).join('');
}

function applyPatrimonioFiltersAndRender() {
    if(!patrimonioFullList) return;
    const tipo = filtroTipoUnidadeEl.value;
    const unidade = filtroUnidadeEl.value;
    const estado = filtroEstadoEl.value;
    const busca = normalizeStr(filtroBuscaEl.value);

    patrimonioFilteredList = patrimonioFullList.filter(item => {
        const descMatch = !busca || normalizeStr(item.Descrição).includes(busca);
        const tomboMatch = !busca || normalizeStr(item.Tombamento).includes(busca);
        const localMatch = !busca || normalizeStr(item.Localização).includes(busca);

        return (!tipo || item.Tipo === tipo) &&
               (!unidade || item.Unidade === unidade) &&
               (!estado || getNormalizedEstado(item.Estado) === estado) &&
               (descMatch || tomboMatch || localMatch);
    });
    patrimonioCurrentPage = 1;
    renderPatrimonioTable();
}

function renderPatrimonioTable() {
    const startIndex = (patrimonioCurrentPage - 1) * patrimonioItemsPerPage;
    const itemsToDisplay = patrimonioFilteredList.slice(startIndex, startIndex + patrimonioItemsPerPage);
    
    const actionButtonsHTML = (itemId) => !isLoggedIn ? '' : `<td class="px-3 py-2 space-x-2"><button class="transfer-btn p-1 text-green-600 hover:text-green-800" data-id="${itemId}" title="Transferir Item"><svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" viewBox="0 0 16 16"><path fill-rule="evenodd" d="M1.5 1.5A.5.5 0 0 0 1 2v4.8a2.5 2.5 0 0 0 2.5 2.5h9.793l-3.347 3.346a.5.5 0 0 0 .708.708l4.2-4.2a.5.5 0 0 0 0-.708l-4-4a.5.5 0 0 0-.708.708L13.293 8.3H3.5a1.5 1.5 0 0 1-1.5-1.5V2a.5.5 0 0 0-.5-.5z"/></svg></button><button class="edit-btn p-1 text-blue-600 hover:text-blue-800" data-id="${itemId}" title="Editar Item"><svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" viewBox="0 0 16 16"><path d="M15.502 1.94a.5.5 0 0 1 0 .706L14.459 3.69l-2-2L13.502.646a.5.5 0 0 1 .707 0l1.293 1.293zm-1.75 2.456-2-2L4.939 9.21a.5.5 0 0 0-.121.196l-.805 2.414a.25.25 0 0 0 .316.316l2.414-.805a.5.5 0 0 0 .196-.12l6.813-6.814z"/><path fill-rule="evenodd" d="M1 13.5A1.5 1.5 0 0 0 2.5 15h11a1.5 1.5 0 0 0 1.5-1.5v-6a.5.5 0 0 0-1 0v6a.5.5 0 0 1-.5.5h-11a.5.5 0 0 1-.5-.5v-11a.5.5 0 0 1 .5-.5H9a.5.5 0 0 0 0-1H2.5A1.5 1.5 0 0 0 1 2.5z"/></svg></button><button class="delete-btn p-1 text-red-600 hover:text-red-800" data-id="${itemId}" title="Excluir Item"><svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" fill="currentColor" viewBox="0 0 16 16"><path d="M5.5 5.5A.5.5 0 0 1 6 6v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m2.5 0a.5.5 0 0 1 .5.5v6a.5.5 0 0 1-1 0V6a.5.5 0 0 1 .5-.5m3 .5a.5.5 0 0 0-1 0v6a.5.5 0 0 0 1 0z"/><path d="M14.5 3a1 1 0 0 1-1 1H13v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V4h-.5a1 1 0 0 1-1-1V2a1 1 0 0 1 1-1H6a1 1 0 0 1 1-1h2a1 1 0 0 1 1 1h3.5a1 1 0 0 1 1 1zM4.118 4 4 4.059V13a1 1 0 0 0 1 1h6a1 1 0 0 0 1-1V4.059L11.882 4zM2.5 3h11V2h-11z"/></svg></button></td>`;

    tableBodyEl.innerHTML = itemsToDisplay.length === 0 
        ? `<tr><td colspan="${isLoggedIn ? 7 : 6}" class="text-center py-10 text-slate-500">Nenhum item encontrado com os filtros atuais.</td></tr>`
        : itemsToDisplay.map(item => `
            <tr class="border-b border-slate-200 hover:bg-slate-50">
                <td class="px-3 py-2 font-mono text-xs">${item.Tombamento || 'S/T'}</td>
                <td class="px-3 py-2 font-medium text-slate-900">${item.Descrição || 'N/A'}</td>
                <td class="px-3 py-2">${item.Unidade || 'N/A'}</td>
                <td class="px-3 py-2 text-xs">${item.Fornecedor || 'N/A'}</td>
                <td class="px-3 py-2 text-xs">${item['Origem da Doação'] || 'N/A'}</td>
                <td class="px-3 py-2"><span class="badge ${getStateColor(item.Estado)}">${item.Estado || 'N/A'}</span></td>
                ${actionButtonsHTML(item.id)}
            </tr>`).join('');
    renderPatrimonioPagination();
}

function renderPatrimonioPagination() {
    const totalPages = Math.ceil(patrimonioFilteredList.length / patrimonioItemsPerPage);
    const startItem = (patrimonioCurrentPage - 1) * patrimonioItemsPerPage + 1;
    const endItem = Math.min(startItem + patrimonioItemsPerPage - 1, patrimonioFilteredList.length);
    
    paginationSummaryEl.textContent = patrimonioFilteredList.length > 0 ? `Mostrando ${startItem}-${endItem} de ${patrimonioFilteredList.length} itens.` : 'Nenhum item para exibir.';

    paginationControlsEl.innerHTML = totalPages <= 1 ? '' : `<div class="inline-flex"><button data-page="${patrimonioCurrentPage - 1}" class="px-4 py-2 text-sm border rounded-l-lg" ${patrimonioCurrentPage === 1 ? 'disabled' : ''}>Anterior</button><button data-page="${patrimonioCurrentPage + 1}" class="px-4 py-2 text-sm border rounded-r-lg" ${patrimonioCurrentPage === totalPages ? 'disabled' : ''}>Próximo</button></div>`;
}

// --- LÓGICA DO DASHBOARD, HISTÓRICO, NOTAS FISCAIS ---

function renderDashboard(items) {
    if (!items || items.length === 0) return;
    const kpi = (id, value) => document.getElementById(id).textContent = value;
    kpi('kpi-total-itens', items.reduce((s, i) => s + (i.Quantidade || 1), 0));
    kpi('kpi-total-unidades', new Set(items.map(i => i.Unidade)).size);
    const estadosCount = items.reduce((a, i) => { const n = getNormalizedEstado(i.Estado); a[n] = (a[n] || 0) + (i.Quantidade || 1); return a; }, {});
    kpi('kpi-total-avariados', estadosCount['Avariado'] || 0);
    kpi('kpi-total-novos', estadosCount['Novo'] || 0);

    const estadoCtx = document.getElementById('dashboardEstadoChart').getContext('2d');
    if (dashboardEstadoChart) dashboardEstadoChart.destroy();
    dashboardEstadoChart = new Chart(estadoCtx, { type: 'doughnut', data: { labels: Object.keys(estadosCount), datasets: [{ data: Object.values(estadosCount), backgroundColor: ['#ef4444', '#10b981', '#3b82f6', '#f59e0b'] }] }, options: { responsive: true, maintainAspectRatio: false } });

    const unidadesCount = items.reduce((a, i) => { const u = i.Unidade || 'N/D'; a[u] = (a[u] || 0) + 1; return a; }, {});
    const sortedUnidades = Object.entries(unidadesCount).sort(([,a],[,b]) => b-a).slice(0, 10);
    const tipoCtx = document.getElementById('dashboardTipoChart').getContext('2d');
    if (dashboardTipoChart) dashboardTipoChart.destroy();
    dashboardTipoChart = new Chart(tipoCtx, { type: 'bar', data: { labels: sortedUnidades.map(u => u[0]), datasets: [{ label: 'Itens', data: sortedUnidades.map(u => u[1]), backgroundColor: '#3b82f6' }] }, options: { indexAxis: 'y', responsive: true, maintainAspectRatio: false } });
}

function renderHistory() {
    if(!isLoggedIn) {
        historyContainer.innerHTML = `<p class="text-slate-500">Acesso negado.</p>`;
        return;
    }
    historyContainer.innerHTML = historicoFullList.length > 0 
        ? historicoFullList.map(h => `
            <div class="p-3 border rounded-md bg-slate-50 text-sm">
                <p><strong>${h.action}:</strong> ${h.itemDesc || ''} <span class="text-xs text-slate-500">(${h.itemId || ''})</span></p>
                <p class="text-xs text-slate-600">${h.details}</p>
                <div class="text-right text-xs text-slate-400 mt-1">${h.user} em ${h.timestamp ? new Date(h.timestamp.seconds * 1000).toLocaleString('pt-BR') : ''}</div>
            </div>
        `).join('')
        : `<p class="text-slate-500">Nenhum histórico encontrado.</p>`;
}

function populateNfTab() {
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
    renderNfList();
}

function renderNfList() {
    const container = document.getElementById('lista-notas');
    container.innerHTML = '';
    if (Object.keys(processedNfData).length === 0) return; 

    const tomboMap = new Map(patrimonioFullList.map(item => [item.Tombamento?.trim(), item]));
    
    const nfSearchTerm = document.getElementById('nf-search-index').value.toLowerCase();
    const nfItemSearchTerm = document.getElementById('nf-item-search-index').value.toLowerCase();
    const nfTipoEntrada = document.getElementById('nf-tipo-entrada-index').value;
    const startDateStr = document.getElementById('nf-date-start-index').value;
    const endDateStr = document.getElementById('nf-date-end-index').value;

    const startDate = startDateStr ? new Date(startDateStr) : null;
    let endDate = endDateStr ? new Date(endDateStr) : null;
    if (endDate) { endDate.setHours(23, 59, 59, 999); }
    if (startDate) { startDate.setHours(0, 0, 0, 0); }

    const filteredNfs = Object.keys(processedNfData).filter(nf => {
        const nfGroup = processedNfData[nf];
        if (nfSearchTerm && !nf.toLowerCase().includes(nfSearchTerm)) return false;
        if (nfItemSearchTerm) {
            if (!nfGroup.items.some(item => (item.Descrição || '').toLowerCase().includes(nfItemSearchTerm) || (item.Espécie || '').toLowerCase().includes(nfItemSearchTerm))) return false;
        }
        if (nfTipoEntrada && nfGroup.tipoEntrada !== nfTipoEntrada) return false;
        const nfDate = parsePtBrDate(nfGroup.dataCadastro);
        if (startDate && nfDate < startDate) return false;
        if (endDate && nfDate > endDate) return false;
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
            const nfGroup = processedNfData[nf];
            const itemSummaryText = nfGroup.items.slice(0, 2).map(i => escapeHtml(i.Descrição || i.Espécie)).join(', ') + (nfGroup.items.length > 2 ? '...' : '');
            const nfDetails = document.createElement('details');
            nfDetails.className = 'bg-white rounded-lg shadow-sm border mb-3 border-t-0 rounded-t-none';
            nfDetails.innerHTML = `
                <summary class="p-4 font-semibold cursor-pointer grid grid-cols-1 md:grid-cols-3 gap-4 items-center hover:bg-slate-50">
                    <div class="md:col-span-2">
                        <p class="text-xs text-slate-500">NF: <strong class="text-blue-700 text-sm">${escapeHtml(nf)}</strong> | Fornecedor: <strong>${escapeHtml(nfGroup.fornecedor)}</strong></p>
                        <p class="text-xs text-slate-500 mt-1 truncate">Itens: ${itemSummaryText}</p>
                    </div>
                    <div><p class="text-xs text-slate-500">Data Cadastro</p><strong>${escapeHtml(nfGroup.dataCadastro)}</strong></div>
                </summary>
                <div class="p-4 border-t border-slate-200 space-y-2">
                    ${nfGroup.items.map(item => {
                        const tombo = item.TOMBAMENTO?.trim();
                        const allocatedItem = tombo ? tomboMap.get(tombo) : undefined;
                        let allocationHtml = `<span class="px-2 py-1 text-xs font-semibold text-slate-700 bg-slate-200 rounded-full">Não Alocado</span>`;
                        if (allocatedItem) {
                            allocationHtml = `<div><span class="px-2 py-1 text-xs font-semibold text-green-800 bg-green-100 rounded-full">Alocado</span><p class="text-xs text-slate-600 mt-1 text-right">→ <strong>${escapeHtml(allocatedItem.Unidade)}</strong> (${escapeHtml(allocatedItem.Tipo)})</p></div>`;
                        }
                        return `<div class="p-3 border rounded-md flex justify-between items-center bg-slate-50/50">
                                    <div class="flex-1"><p class="font-bold text-slate-800">${escapeHtml(item.Descrição || item.Espécie)}</p><p class="text-sm text-slate-500">Tombamento: <span class="font-mono">${escapeHtml(tombo || 'N/D')}</span></p></div>
                                    <div class="text-right ml-4">${allocationHtml}</div>
                                </div>`;
                    }).join('')}
                </div>
            `;
            container.appendChild(nfDetails);
        });
    });
}

const getNormalizedEstado = (estadoStr) => {
    const normalized = normalizeStr(estadoStr);
    if (['avariado', 'quebrado', 'defeito', 'danificado', 'ruim'].some(k => normalized.includes(k))) return 'Avariado';
    if (normalized === 'novo') return 'Novo';
    if (normalized === 'bom' || normalized === 'otimo') return 'Bom';
    if (normalized === 'regular') return 'Regular';
    return 'Avariado';
};

function getStateColor(state) {
    const normalizedEstado = getNormalizedEstado(state);
    return { 'Novo': 'badge-green', 'Bom': 'badge-blue', 'Regular': 'badge-yellow', 'Avariado': 'badge-red' }[normalizedEstado] || 'bg-slate-200';
}

// --- LÓGICA DE MODAIS E FORMULÁRIOS ---

const openModal = (modalEl) => { if (modalEl) { modalEl.classList.remove('hidden'); setTimeout(() => { modalEl.querySelector('.modal-overlay')?.classList.remove('opacity-0'); modalEl.querySelector('.modal-container')?.classList.remove('opacity-0', 'scale-95'); }, 10); } };
const closeModal = (modalEl) => { if (modalEl) { modalEl.querySelector('.modal-overlay')?.classList.add('opacity-0'); modalEl.querySelector('.modal-container')?.classList.add('opacity-0', 'scale-95'); setTimeout(() => { modalEl.classList.add('hidden'); }, 300); } };

function openItemModal(item = null) {
    itemForm.reset();
    document.getElementById('modal-title').textContent = item ? 'Editar Item' : 'Adicionar Novo Item';
    document.getElementById('item-id').value = item ? item.id : '';
    if (item) {
        Object.keys(item).forEach(key => {
            const formKey = `item-${key.toLowerCase().replace(/\s/g, '-').replace('ç', 'c').replace('ã', 'a')}`;
            const element = document.getElementById(formKey);
            if (element) element.value = item[key];
        });
    }
    openModal(itemModal);
}

async function logAction(action, details) {
    if (!isLoggedIn) return;
    try {
        await addDoc(collection(db, 'historico'), { ...details, action: action, user: auth.currentUser.email, timestamp: serverTimestamp() });
    } catch (error) { console.error("Falha ao registrar ação no histórico:", error); }
}

async function handleFormSubmit(e) {
    e.preventDefault(); if(!isLoggedIn) return;
    const id = itemForm['item-id'].value;
    const itemData = { Tombamento: itemForm['item-tombamento'].value, Tipo: itemForm['item-tipo'].value, 'Descrição': itemForm['item-descricao'].value, Unidade: itemForm['item-unidade'].value, Quantidade: parseInt(itemForm['item-quantidade'].value), Localização: itemForm['item-localizacao'].value, Estado: itemForm['item-estado'].value, Fornecedor: itemForm['item-fornecedor'].value, 'Origem da Doação': itemForm['item-origem-da-doacao'].value, Observação: itemForm['item-observacao'].value, updatedAt: serverTimestamp() };
    const action = id ? 'Edição' : 'Criação';
    try {
        if (id) await updateDoc(doc(db, 'patrimonio', id), itemData);
        else { itemData.createdAt = serverTimestamp(); await addDoc(collection(db, 'patrimonio'), itemData); }
        logAction(action, { itemId: id || 'novo', itemDesc: itemData['Descrição'], details: `Item ${id ? 'editado' : 'criado'}: ${itemData['Descrição']}` });
        closeModal(itemModal); await idb.metadata.clear(); loadAllData(true);
    } catch (error) { console.error("Erro ao salvar o item: ", error); showNotification('Erro ao salvar!', 'error');}
}

function openDeleteModal(id) {
    const item = patrimonioFullList.find(i => i.id === id); if (!item) return;
    document.getElementById('delete-item-info').textContent = `${item.Descrição} (Tomb: ${item.Tombamento || 'S/T'})`;
    confirmDeleteBtn.dataset.id = id;
    openModal(deleteConfirmModal);
}

async function handleDelete() {
    if(!isLoggedIn) return;
    const id = confirmDeleteBtn.dataset.id;
    const item = patrimonioFullList.find(i => i.id === id);
    try {
        await deleteDoc(doc(db, 'patrimonio', id));
        logAction('Exclusão', { itemId: id, itemDesc: item.Descrição, details: `Item excluído: ${item.Descrição}` });
        closeModal(deleteConfirmModal); await idb.metadata.clear(); loadAllData(true);
    } catch(error) { console.error("Erro ao excluir item: ", error); showNotification('Erro ao excluir!', 'error'); }
}

function openTransferModal(id) {
    const item = patrimonioFullList.find(i => i.id === id); if (!item) return;
    transferForm.reset();
    transferForm['transfer-item-id'].value = id;
    document.getElementById('transfer-item-description').textContent = item.Descrição;
    document.getElementById('transfer-item-current-unit').textContent = `${item.Unidade} (${item.Localização || 'N/D'})`;
    const tipos = [...new Set(patrimonioFullList.map(i => i.Tipo).filter(Boolean))].sort();
    transferForm['transfer-tipo'].innerHTML = '<option value="">Selecione um Tipo</option>' + tipos.map(t => `<option value="${t}">${t}</option>`).join('');
    openModal(transferModal);
}

function updateUnidadeFilter(tipoSelectEl, unidadeSelectEl) {
    const selectedTipo = tipoSelectEl.value;
    unidadeSelectEl.innerHTML = selectedTipo ? '<option value="">TODAS AS UNIDADES</option>' + [...new Set(patrimonioFullList.filter(i => i.Tipo === selectedTipo).map(i => i.Unidade).filter(Boolean))].sort().map(u => `<option value="${u}">${u}</option>`).join('') : '<option value="">Selecione um Tipo</option>';
    unidadeSelectEl.disabled = !selectedTipo;
}

async function handleTransferSubmit(e) {
    e.preventDefault(); if(!isLoggedIn) return;
    const id = transferForm['transfer-item-id'].value;
    const newUnidade = transferForm['transfer-unidade'].value;
    const originalItem = patrimonioFullList.find(i => i.id === id);
    const updatedData = { Tipo: transferForm['transfer-tipo'].value, Unidade: newUnidade, Localização: transferForm['transfer-localizacao'].value, updatedAt: serverTimestamp() };
    try {
        await updateDoc(doc(db, 'patrimonio', id), updatedData);
        logAction('Transferência', { itemId: id, itemDesc: originalItem.Descrição, details: `De '${originalItem.Unidade}' para '${newUnidade}'` });
        closeModal(transferModal); await idb.metadata.clear(); loadAllData(true);
    } catch (error) { console.error("Erro ao transferir item:", error); showNotification('Erro ao transferir!', 'error');}
}

function switchTab(tabName) {
    if(tabName === 'edit') return;
    navButtons.forEach(btn => btn.classList.toggle('active', btn.dataset.tab === tabName));
    contentPanes.forEach(pane => pane.classList.toggle('hidden', pane.id !== `content-${tabName}`));
    if (tabName === 'dashboard' && patrimonioFullList.length > 0) renderDashboard(patrimonioFullList);
    if (tabName === 'historico') renderHistory();
    if (tabName === 'notas') renderNfList();
}

async function handleLoginFormSubmit(e) {
    e.preventDefault();
    const email = document.getElementById('login-email').value;
    const password = document.getElementById('login-password').value;
    if (!email || !password) { showNotification('Preencha e-mail e senha.', 'error'); return; }
    
    const loginBtn = document.getElementById('btn-login'), btnText = document.getElementById('login-btn-text'), btnSpinner = document.getElementById('login-btn-spinner');
    loginBtn.disabled = true; btnText.classList.add('hidden'); btnSpinner.classList.remove('hidden');

    const loginErrorEl = loginForm.querySelector('#login-error');
    loginErrorEl.classList.add('hidden');
    
    const result = await handleLogin(email, password);
    if (result === true) {
        closeModal(loginModal);
    } else {
        let errorMessage = "Ocorreu um erro desconhecido.";
        switch (result.code) {
            case 'auth/user-not-found': case 'auth/wrong-password': case 'auth/invalid-credential': errorMessage = "E-mail ou senha incorretos."; break;
            case 'auth/invalid-email': errorMessage = "O formato do e-mail é inválido."; break;
            case 'auth/too-many-requests': errorMessage = "Acesso bloqueado por muitas tentativas."; break;
        }
        loginErrorEl.textContent = errorMessage;
        loginErrorEl.classList.remove('hidden');
    }
    loginBtn.disabled = false; btnText.classList.remove('hidden'); btnSpinner.classList.add('hidden');
}

// --- EVENT LISTENERS ---
document.addEventListener('DOMContentLoaded', () => {
    // Adiciona o listener de autenticação
    addAuthListener(user => {
        isLoggedIn = !!user;
        updateUIVisibility();
        if (isLoggedIn) {
            loadHistory();
            document.getElementById('tab-notas').style.display = 'inline-block';
        } else {
            document.getElementById('tab-notas').style.display = 'none';
        }
    });

    // Inicia o carregamento dos dados
    loadAllData();
    
    // Listeners de filtros
    const debouncedFilter = debounce(applyPatrimonioFiltersAndRender, 300);
    filtroTipoUnidadeEl.addEventListener('change', () => { updateUnidadeFilter(filtroTipoUnidadeEl, filtroUnidadeEl); debouncedFilter(); });
    [filtroUnidadeEl, filtroEstadoEl].forEach(el => el.addEventListener('change', debouncedFilter));
    filtroBuscaEl.addEventListener('input', debouncedFilter);
    resetFiltersBtn.addEventListener('click', () => { document.getElementById('patrimonio-filters-form').reset(); filtroUnidadeEl.disabled = true; applyPatrimonioFiltersAndRender(); });

    // Listeners da aba Notas Fiscais
    const debouncedRenderNf = debounce(renderNfList, 300);
    document.getElementById('nf-search-index').addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-item-search-index').addEventListener('input', debouncedRenderNf);
    document.getElementById('nf-tipo-entrada-index').addEventListener('change', renderNfList);
    document.getElementById('nf-date-start-index').addEventListener('change', renderNfList);
    document.getElementById('nf-date-end-index').addEventListener('change', renderNfList);
    document.getElementById('clear-filters-nf-index').addEventListener('click', () => {
        document.getElementById('nf-search-index').value = ''; document.getElementById('nf-item-search-index').value = ''; document.getElementById('nf-tipo-entrada-index').value = ''; document.getElementById('nf-date-start-index').value = ''; document.getElementById('nf-date-end-index').value = '';
        renderNfList();
    });

    // Outros listeners
    paginationControlsEl.addEventListener('click', (e) => { if(e.target.dataset.page) { patrimonioCurrentPage = parseInt(e.target.dataset.page); renderPatrimonioTable(); }});
    tableBodyEl.addEventListener('click', (e) => {
        const btn = e.target.closest('button'); if (!btn || !isLoggedIn) return;
        const id = btn.dataset.id;
        if (btn.classList.contains('edit-btn')) openItemModal(patrimonioFullList.find(i => i.id === id));
        if (btn.classList.contains('delete-btn')) openDeleteModal(id);
        if (btn.classList.contains('transfer-btn')) openTransferModal(id);
    });
    
    openAddModalBtn.addEventListener('click', () => openItemModal());
    itemForm.addEventListener('submit', handleFormSubmit);
    loginForm.addEventListener('submit', handleLoginFormSubmit);
    openLoginModalBtn.addEventListener('click', () => openModal(loginModal));
    logoutBtn.addEventListener('click', handleLogout);
    transferForm.addEventListener('submit', handleTransferSubmit);
    document.getElementById('transfer-tipo').addEventListener('change', (e) => updateUnidadeFilter(e.target, transferForm['transfer-unidade']));
    confirmDeleteBtn.addEventListener('click', handleDelete);
    
    navButtons.forEach(button => button.addEventListener('click', (e) => {
        e.preventDefault();
        if(e.currentTarget.tagName === 'BUTTON') { switchTab(button.dataset.tab); } 
        else if (e.currentTarget.tagName === 'A') { window.open(e.currentTarget.href, '_blank'); }
    }));

    document.addEventListener('click', (e) => { if (e.target.matches('.js-close-modal') || e.target.matches('.modal-overlay')) { closeModal(e.target.closest('.modal')); } });
    document.getElementById('force-refresh-btn-index').addEventListener('click', () => { showNotification('Forçando atualização do servidor...', 'info'); loadAllData(true); });
});
