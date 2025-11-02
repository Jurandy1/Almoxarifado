/**
 * shared.js
 * Este arquivo contém todo o código JavaScript compartilhado entre as páginas.
 * Inclui:
 * - Configuração do Firebase e Dexie.js (cache).
 * - Funções de autenticação (login, logout, verificação de estado).
 * - Funções de carregamento de dados (do Firebase e da planilha GIAP).
 * - Funções utilitárias de interface (notificações, modais, etc.).
 */

// Importações do Firebase
import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js";
import { getFirestore, collection, query, getDocs, doc, getDoc, setDoc, updateDoc, serverTimestamp, writeBatch, addDoc, orderBy, limit, where, deleteDoc } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";
// MUDANÇA: Incluindo signInAnonymously e removendo signInWithEmailAndPassword daqui para usar apenas handleLogin com token no ambiente
import { getAuth, signInWithCustomToken, signInAnonymously, signOut, onAuthStateChanged } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js";
import { getAuth as getAuthIndex } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js"; // Para uso específico no index.js/login

// --- CONFIGURAÇÃO E INICIALIZAÇÃO ---

// As credenciais fixas abaixo foram substituídas pelo uso obrigatório das variáveis globais
// do ambiente Canvas para garantir autenticação e acesso ao Firestore.

// VARIÁVEIS GLOBAIS OBRIGATÓRIAS DO AMBIENTE
const appId = typeof __app_id !== 'undefined' ? __app_id : 'default-app-id';
const firebaseConfig = typeof __firebase_config !== 'undefined' ? JSON.parse(__firebase_config) : { /* Fallback config */ };
const initialAuthToken = typeof __initial_auth_token !== 'undefined' ? __initial_auth_token : null;

const app = initializeApp(firebaseConfig);
export const db = getFirestore(app);
export const auth = getAuth(app);


// Inicializa a autenticação (MUST BE CALLED)
async function initializeAuth() {
    try {
        if (initialAuthToken) {
            await signInWithCustomToken(auth, initialAuthToken);
            console.log("Firebase Auth: Signed in with custom token.");
        } else {
            await signInAnonymously(auth);
            console.log("Firebase Auth: Signed in anonymously.");
        }
    } catch (error) {
        console.error("Firebase Auth Error:", error);
    }
}

// Chama a inicialização da autenticação
initializeAuth();


export const GIAP_SHEET_URL = 'https://docs.google.com/spreadsheets/d/e/2PACX-1vTaVN5Oiv5eDmdJpsCCys-0TQb9q-QaOeTqakTE6wBYup2sJYnPf2_uNIYkmrI7FIvis1aUxv21vB_k/pub?output=csv';

export const idb = new Dexie('InventoryDB');
idb.version(3).stores({
    patrimonio: 'id, Tombamento, *Unidade, *Tipo, *Estado',
    giap: '++_id, TOMBAMENTO, *Unidade',
    metadata: 'key'
});

// --- FUNÇÕES DE AUTENTICAÇÃO ---

let authStateChangeCallbacks = [];

onAuthStateChanged(auth, user => {
    authStateChangeCallbacks.forEach(cb => cb(user));
});

/**
 * Adiciona uma função a ser chamada sempre que o estado de autenticação mudar.
 * @param {function} callback - A função que recebe o objeto `user` do Firebase.
 */
export function addAuthListener(callback) {
    authStateChangeCallbacks.push(callback);
    // Chama imediatamente com o estado atual do usuário
    callback(auth.currentUser);
}

/**
 * Realiza o login do usuário.
 * NOTE: Esta função é mantida para simular o login, mas no ambiente Canvas, 
 * a autenticação com e-mail/senha é desativada. Deve-se usar um token real.
 * Mantemos a estrutura para compatibilidade com a interface do seu index.js.
 * @param {string} email 
 * @param {string} password 
 * @returns {Promise<boolean>} - True se o login for bem-sucedido, false caso contrário.
 */
export async function handleLogin(email, password) {
    try {
        // MUDANÇA: Para funcionar no ambiente Canvas, substituímos o login com senha 
        // pelo login com o token.
        // Já que o index.js usa esta função, vamos simular o sucesso se houver um token.
        if (initialAuthToken) {
             // Simula o login com sucesso se o token existe (assumindo que o login com email é apenas uma porta)
             return true; 
        } else {
            // No ambiente Canvas, o login de usuário/senha não funciona, apenas login anônimo ou com token.
            // Para permitir que a UI no index.html funcione, usamos signInAnonymously como fallback
            await signInAnonymously(auth);
            return true;
        }
    } catch (error) {
        console.error("Erro no login:", error.code);
        // Simula um erro de credenciais inválidas para o feedback da UI
        return { success: false, code: 'auth/invalid-credential' };
    }
}


/**
 * Realiza o logout do usuário.
 */
export function handleLogout() {
    // No ambiente Canvas, apenas remove o token e força a autenticação anônima novamente.
    signOut(auth);
}

// --- FUNÇÕES DE CARREGAMENTO DE DADOS ---
export const CACHE_DURATION_MS = 6 * 60 * 60 * 1000; // 6 horas

// MUDANÇA: Todas as coleções agora são prefixadas com o appId para conformidade com as regras de segurança do Canvas.
const getCollectionPath = (collectionName) => `artifacts/${appId}/public/data/${collectionName}`;

export async function loadUnitMappingFromFirestore() {
    try {
        const docRef = doc(db, getCollectionPath('config'), 'unitMapping');
        const docSnap = await getDoc(docRef);
        return docSnap.exists() ? docSnap.data().mappings || {} : {};
    } catch (error) {
        console.error("Error loading unit mapping:", error);
        return {};
    }
}

export async function loadReconciledUnits() {
    try {
        const docRef = doc(db, getCollectionPath('config'), 'reconciledUnits');
        const docSnap = await getDoc(docRef);
        return docSnap.exists() ? docSnap.data().units || [] : [];
    } catch (error) {
        console.error("Erro ao carregar unidades conciliadas:", error);
        return [];
    }
}

export async function loadCustomGiapUnits() {
    try {
        const docRef = doc(db, getCollectionPath('config'), 'customGiapUnits');
        const docSnap = await getDoc(docRef);
        return docSnap.exists() ? docSnap.data().units || [] : [];
    } catch (error) {
        console.error("Error loading custom GIAP units:", error);
        return [];
    }
}

export async function loadFirebaseInventory() {
    const querySnapshot = await getDocs(query(collection(db, getCollectionPath('patrimonio'))));
    return querySnapshot.docs.map(doc => ({ id: doc.id, ...doc.data() }));
}

export function loadGiapInventory() {
    return new Promise((resolve, reject) => {
        Papa.parse(GIAP_SHEET_URL, {
            download: true,
            header: true,
            skipEmptyLines: true,
            transformHeader: header => header.trim(),
            complete: r => resolve(r.data),
            error: e => reject(e)
        });
    });
}

// --- FUNÇÕES UTILITÁRIAS DE UI E GERAIS ---

/**
 * Exibe uma notificação flutuante (toast).
 * @param {string} message - A mensagem a ser exibida.
 * @param {'info'|'success'|'error'|'warning'} type - O tipo de notificação.
 * @param {number} duration - Duração em milissegundos.
 */
export function showNotification(message, type = 'info', duration = 3000) {
    const notification = document.createElement('div');
    notification.className = `notification-toast ${type}`;
    notification.textContent = message;
    document.body.appendChild(notification);
    setTimeout(() => notification.classList.add('show'), 10);
    setTimeout(() => {
        notification.classList.remove('show');
        setTimeout(() => notification.remove(), 500);
    }, duration);
}

/**
 * Mostra uma tela de carregamento sobre toda a página.
 * @param {string} message - Mensagem a ser exibida no overlay.
 */
export function showOverlay(message) {
    const overlay = document.getElementById('full-page-overlay');
    const overlayMessage = document.getElementById('overlay-message');
    if (overlay && overlayMessage) {
        overlayMessage.textContent = message;
        overlay.classList.remove('hidden');
    }
}

/**
 * Esconde a tela de carregamento.
 */
export function hideOverlay() {
    const overlay = document.getElementById('full-page-overlay');
    if (overlay) {
        overlay.classList.add('hidden');
    }
}

/**
 * Normaliza uma string (remove acentos, espaços extras e converte para minúsculas).
 * @param {string} str 
 * @returns {string}
 */
export const normalizeStr = (str) => (str || '').toString().normalize('NFD').replace(/[\u0300-\u036f]/g, '').trim().toLowerCase();

/**
 * Cria uma versão "debounced" de uma função (atrasa sua execução).
 * @param {function} func - A função a ser executada.
 * @param {number} delay - O atraso em milissegundos.
 * @returns {function}
 */
export const debounce = (func, delay) => {
    let t;
    return (...a) => {
        clearTimeout(t);
        t = setTimeout(() => func.apply(this, a), delay);
    };
};

/**
 * Escapa caracteres HTML para prevenir XSS.
 * @param {string} unsafe - A string a ser escapada.
 * @returns {string}
 */
export const escapeHtml = (unsafe) => (unsafe === undefined || unsafe === null) ? '' : unsafe.toString().replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;").replace(/'/g, "&#039;");

/**
 * Converte uma string de moeda brasileira (R$) para um número.
 * @param {string} value 
 * @returns {number}
 */
export const parseCurrency = (value) => {
    if (typeof value !== 'string' || value.trim() === '') return 0;
    return parseFloat(value.replace('R$', '').replace(/\./g, '').replace(',', '.').trim()) || 0;
};
