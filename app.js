/* Douala Flow AI : application d'analyse des flux de transport urbain à Douala.
   Carte Leaflet + OpenStreetMap, base Supabase, itinéraires OSRM, collecte GPS par les téléphones. */
(function () {
'use strict';
const CFG = window.DFA_CONFIG;
const $ = s => document.querySelector(s), $$ = s => Array.from(document.querySelectorAll(s));
const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const ic = n => `<svg class="ic"><use href="#i-${n}"/></svg>`;
const DAYS = ['Lundi','Mardi','Mercredi','Jeudi','Vendredi','Samedi','Dimanche'];
const LN = ['', 'Fluide', 'Modéré', 'Dense', 'Très dense'], LC = ['', '#1e9e5a', '#e0a800', '#e8701a', '#d42f2f'];
const lvl = x => x < 35 ? 1 : x < 55 ? 2 : x < 75 ? 3 : 4;
const pill = x => `<span class="pill p${lvl(x)}">${LN[lvl(x)]}</span>`;
const clamp = (x, a = 0, b = 100) => Math.max(a, Math.min(b, x));
const fmtMin = m => m < 60 ? `${Math.round(m)} min` : `${Math.floor(m / 60)} h ${String(Math.round(m % 60)).padStart(2, '0')}`;
const fmtKm = m => (m / 1000).toFixed(1).replace('.', ',') + ' km';
const dow = d => (d.getDay() + 6) % 7;
const fmtDate = s => new Date(s).toLocaleString('fr-FR', {day: '2-digit', month: '2-digit', hour: '2-digit', minute: '2-digit'});
const SRC = {gps: ['gps', 'Temps réel'], hist: ['hist', 'Historique'], model: ['', 'Modèle']};
let toastT; function toast(m) { const t = $('#toast'); t.textContent = m; t.hidden = false; clearTimeout(toastT); toastT = setTimeout(() => { t.hidden = true; }, 3600); }
const ls = {get(k) { try { return JSON.parse(localStorage.getItem(k)); } catch (e) { return null; } }, set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }};

/* ---------- Données de référence (repli si la base est injoignable) ---------- */
const ZONES = {1: 'Bonabéri', 2: 'Centre', 3: 'Deïdo–Bépanda', 4: 'Nord', 5: 'Ndokoti', 6: 'Est'};
const NODES = [['Bonabéri', 4.0745, 9.6680], ['Deïdo', 4.0655, 9.7075], ['Akwa', 4.0510, 9.6975], ['Bonanjo', 4.0405, 9.6890], ['Bali', 4.0385, 9.6995], ['New Bell', 4.0345, 9.7120], ['Aéroport', 4.0125, 9.7175], ['Bépanda', 4.0620, 9.7225], ['Bonamoussadi', 4.0890, 9.7370], ['Makepe', 4.0790, 9.7500], ['Ndokoti', 4.0450, 9.7400], ['Logbaba', 4.0420, 9.7650], ['PK14', 4.0700, 9.7950], ['Village', 4.0230, 9.7600], ['Yassa', 4.0050, 9.7900]];
let AX = [];

/* ---------- Modèle de référence (utilisé seulement en l'absence de mesures) ---------- */
const gs = (h, m, s) => Math.exp(-((h - m) * (h - m)) / (2 * s * s));
function profile(d, h) {
  if (d === 6) return 10 + 25 * gs(h, 11, 2.5) + 28 * gs(h, 17.5, 2.5);
  if (d === 5) return 15 + 30 * gs(h, 8, 1.5) + 50 * gs(h, 12.5, 2.5) + 40 * gs(h, 18, 2);
  return 18 + 62 * gs(h, 7.75, 1.3) + (d === 4 ? 72 : 66) * gs(h, 18.25, 1.6) + 22 * gs(h, 13, 2.2);
}
const model = (a, d, h) => clamp(profile(d, h) * a.coef + 4 * Math.sin(h * 1.7 + a.id * 2.1 + d), 3, 100);

/* ---------- Géométrie ---------- */
const R = 6371000, rad = Math.PI / 180;
const hav = (a, b) => { const dl = (b[0] - a[0]) * rad, dn = (b[1] - a[1]) * rad, q = Math.sin(dl / 2) ** 2 + Math.cos(a[0] * rad) * Math.cos(b[0] * rad) * Math.sin(dn / 2) ** 2; return 2 * R * Math.asin(Math.sqrt(q)); };
function lineLen(l) { let s = 0; for (let i = 1; i < l.length; i++) s += hav(l[i - 1], l[i]); return s; }
// Distance d'un point à une polyligne et abscisse curviligne du projeté (mètres)
function locate(p, line) {
  const k = Math.cos(p[0] * rad), X = q => [(q[1] - p[1]) * k * 111320, (q[0] - p[0]) * 110540];
  let best = {d: Infinity, s: 0}, acc = 0;
  for (let i = 1; i < line.length; i++) {
    const A = X(line[i - 1]), B = X(line[i]), vx = B[0] - A[0], vy = B[1] - A[1], L2 = vx * vx + vy * vy, L = Math.sqrt(L2);
    const t = L2 ? clamp(-(A[0] * vx + A[1] * vy) / L2, 0, 1) : 0, px = A[0] + t * vx, py = A[1] + t * vy, d = Math.hypot(px, py);
    if (d < best.d) best = {d, s: acc + t * L};
    acc += L;
  }
  return best;
}

/* ---------- Supabase ---------- */
const sb = window.supabase.createClient(CFG.supabaseUrl, CFG.supabaseKey);
const S = {user: null, profile: null, obs: [], reports: [], mine: [], gkey: '', tab: 'route', view: 'carte', pick: null, sigType: 'congestion', route: null, sel: 0};
const role = () => S.profile ? S.profile.role : 'visiteur';
async function logAction(a) { if (S.user) await sb.from('logs').insert({action: a}); }

async function loadAxes() {
  const {data, error} = await sb.from('axes').select('*').order('id');
  if (error || !data || !data.length) throw error || new Error('axes');
  const cache = ls.get('dfa_geo3') || {};
  AX = data.map(a => ({...a, zone: ZONES[a.zone_id], geo: a.geometrie || cache[a.id] || a.noeuds}));
  AX.forEach(a => { a.len = lineLen(a.geo); });
}
async function loadObs() {
  const since = new Date(Date.now() - 56 * 864e5).toISOString();
  const {data} = await sb.from('observations').select('axe_id,observed_at,indice,duree_min,vitesse_kmh,source').gte('observed_at', since).order('observed_at', {ascending: false}).limit(5000);
  S.obs = (data || []).map(o => { const t = new Date(o.observed_at); return {...o, t: +t, d: dow(t), h: t.getHours()}; });
}
async function loadReports() {
  const {data} = await sb.from('reports').select('*').eq('status', 'valide').order('created_at', {ascending: false}).limit(200);
  S.reports = data || [];
}
async function loadSettings() { const {data} = await sb.from('settings').select('*'); (data || []).forEach(r => { if (r.key === 'google_maps_key') S.gkey = r.value; }); }

/* Niveau d'un axe : mesures de la dernière heure, sinon historique du même créneau, sinon modèle */
function state(a, d, h, live) {
  if (live) {
    const r = S.obs.filter(o => o.axe_id === a.id && Date.now() - o.t < 3600e3);
    if (r.length) return {v: avg(r.map(o => o.indice)), src: 'gps', n: r.length};
  }
  const hs = S.obs.filter(o => o.axe_id === a.id && o.d === d && o.h === h);
  if (hs.length) return {v: avg(hs.map(o => o.indice)), src: 'hist', n: hs.length};
  return {v: model(a, d, h), src: 'model', n: 0};
}
const avg = l => l.reduce((x, y) => x + y, 0) / l.length;
const travel = (a, v) => a.temps_fluide_min * (1 + v / 45);
const srcTag = s => `<span class="src ${SRC[s][0]}">${SRC[s][1]}</span>`;
function nowDH() { const n = new Date(); return [dow(n), n.getHours()]; }

/* ---------- Carte ---------- */
let map, base = {}, axL = [], nodeL = [], repL, routeL, odL, meL, pickL, recL, gmap;
function initMap() {
  map = L.map('map', {zoomControl: false, attributionControl: true}).setView([4.05, 9.735], 12);
  L.control.zoom({position: 'bottomright'}).addTo(map);
  base.plan = L.tileLayer('https://{s}.basemaps.cartocdn.com/rastertiles/voyager/{z}/{x}/{y}{r}.png', {maxZoom: 19, subdomains: 'abcd', attribution: '&copy; OpenStreetMap &copy; CARTO'});
  base.sat = L.layerGroup([
    L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', {maxZoom: 19, attribution: 'Imagerie &copy; Esri, Maxar, Earthstar Geographics'}),
    L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/Reference/World_Transportation/MapServer/tile/{z}/{y}/{x}', {maxZoom: 19}),
    L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/Reference/World_Boundaries_and_Places/MapServer/tile/{z}/{y}/{x}', {maxZoom: 19})]);
  base.plan.addTo(map);
  AX.forEach((a, i) => {
    const c = L.polyline(a.geo, {color: '#fff', weight: 10, opacity: .9, interactive: false}).addTo(map);
    const l = L.polyline(a.geo, {weight: 6, color: '#999', lineCap: 'round'}).addTo(map);
    l.on('click', e => axisPopup(i, e.latlng));
    axL.push({c, l});
  });
  NODES.forEach(n => nodeL.push(L.marker([n[1], n[2]], {icon: L.divIcon({className: '', html: `<span class="qm"><i style="background:#999"></i>${esc(n[0])}</span>`, iconSize: [0, 0]}), interactive: false, zIndexOffset: 400}).addTo(map)));
  repL = L.layerGroup().addTo(map); routeL = L.layerGroup().addTo(map); odL = L.layerGroup().addTo(map);
  map.fitBounds(L.latLngBounds(NODES.map(n => [n[1], n[2]])).pad(.08));
  map.on('click', onMapClick);
  map.on('zoomend', () => { const z = map.getZoom(); nodeL.forEach(m => m.setOpacity(z >= 12 ? 1 : 0)); });
}
function nodeLevel(n) { const [d, h] = selDH('t'); const near = AX.filter(a => a.noeuds.some(p => Math.abs(p[0] - n[1]) < 1e-4 && Math.abs(p[1] - n[2]) < 1e-4)); return near.length ? Math.max(...near.map(a => state(a, d, h, isNow('t')).v)) : 0; }
function paintAxes() {
  const [d, h] = selDH('t'), live = isNow('t');
  AX.forEach((a, i) => { const s = state(a, d, h, live); axL[i].l.setStyle({color: LC[lvl(s.v)]}); axL[i].c.setLatLngs(a.geo); axL[i].l.setLatLngs(a.geo); });
  NODES.forEach((n, i) => { const v = nodeLevel(n); nodeL[i].setIcon(L.divIcon({className: '', html: `<span class="qm"><i style="background:${LC[lvl(v)] || '#999'}"></i>${esc(n[0])}</span>`, iconSize: [0, 0]})); });
}
function axisPopup(i, at) {
  const a = AX[i], [d, h] = selDH('t'), s = state(a, d, h, isNow('t'));
  L.popup({maxWidth: 260}).setLatLng(at || a.geo[Math.floor(a.geo.length / 2)]).setContent(
    `<b>${esc(a.nom)}</b><br><span style="color:#5d6b7a">${esc(a.troncon)}</span><div style="display:flex;justify-content:space-between;gap:12px;margin-top:8px">${pill(s.v)}<b>${fmtMin(travel(a, s.v))}</b></div><div style="margin-top:6px">${srcTag(s.src)}${s.n ? ` <small style="color:#5d6b7a">${s.n} mesure${s.n > 1 ? 's' : ''}</small>` : ''}</div>`).openOn(map);
}
const RTYPES = {congestion: ['Bouchon', 'car', '#d42f2f'], travaux: ['Travaux', 'cone', '#e0a800'], accident: ['Accident', 'crash', '#b3261e'], perturbation: ['Perturbation', 'wave', '#e8701a'], route_difficile: ['Route difficile', 'road', '#7a5c2e']};
function paintReports() {
  repL.clearLayers();
  S.reports.forEach(r => { const t = RTYPES[r.type] || RTYPES.perturbation; L.marker([r.lat, r.lng], {icon: L.divIcon({className: '', html: `<div class="rp" style="background:${t[2]}">${ic(t[1])}</div>`, iconSize: [30, 30], iconAnchor: [15, 15]}), zIndexOffset: 800}).bindPopup(`<b>${t[0]}</b>${r.description ? '<br>' + esc(r.description) : ''}<br><small>${fmtDate(r.created_at)}</small>`).addTo(repL); });
}
function setBase(k) {
  $$('#layers button').forEach(b => b.classList.toggle('on', b.dataset.l === k));
  if (k === 'google') return showGoogle();
  $('#gmap').hidden = true;
  Object.values(base).forEach(l => map.removeLayer(l)); base[k].addTo(map);
}
function showGoogle() {
  if (!S.gkey) { toast('Vue Google indisponible : la clé Google Maps n\'est pas encore configurée.'); return setBase('plan'); }
  $('#gmap').hidden = false;
  const init = () => {
    if (!gmap) { gmap = new google.maps.Map($('#gmap'), {center: map.getCenter(), zoom: map.getZoom(), mapTypeControl: false, streetViewControl: false, fullscreenControl: false}); new google.maps.TrafficLayer().setMap(gmap); }
    else { gmap.setCenter(map.getCenter()); gmap.setZoom(map.getZoom()); }
  };
  if (window.google && window.google.maps) return init();
  window.__gInit = init;
  const s = document.createElement('script'); s.src = `https://maps.googleapis.com/maps/api/js?key=${encodeURIComponent(S.gkey)}&callback=__gInit&language=fr&region=CM`; s.async = true;
  s.onerror = () => { toast('Impossible de charger Google Maps. Vérifiez la clé.'); setBase('plan'); };
  document.head.appendChild(s);
}
function locateMe(cb) {
  if (!navigator.geolocation) return toast('La géolocalisation n\'est pas disponible sur cet appareil.');
  navigator.geolocation.getCurrentPosition(p => {
    const ll = [p.coords.latitude, p.coords.longitude];
    if (meL) meL.remove(); meL = L.marker(ll, {icon: L.divIcon({className: '', html: '<div class="me"></div>', iconSize: [16, 16], iconAnchor: [8, 8]}), zIndexOffset: 1000}).addTo(map);
    cb ? cb(ll) : map.setView(ll, 15);
  }, () => toast('Position indisponible : autorisez la localisation dans le navigateur.'), {enableHighAccuracy: true, timeout: 12000});
}

// Cadre la carte en tenant compte du panneau (latéral sur ordinateur, en bas sur téléphone)
function fitView(bounds) {
  const p = $('#panel'), mob = innerWidth <= 700;
  map.fitBounds(bounds.pad(.1), mob ? {paddingTopLeft: [20, 70], paddingBottomRight: [20, p.offsetHeight + 10]} : {paddingTopLeft: [p.offsetWidth + 40, 30], paddingBottomRight: [30, 30]});
}

/* ---------- Sélecteurs jour / heure ---------- */
function fillDH(p) {
  $(`#${p}Day`).innerHTML = DAYS.map((d, i) => `<option value="${i}">${d}</option>`).join('');
  $(`#${p}Hour`).innerHTML = '<option value="now">Maintenant</option>' + Array.from({length: 24}, (_, h) => `<option value="${h}">${String(h).padStart(2, '0')} h</option>`).join('');
  $(`#${p}Day`).value = nowDH()[0]; $(`#${p}Hour`).value = 'now';
}
const isNow = p => $(`#${p}Hour`).value === 'now';
function selDH(p) { const [d0, h0] = nowDH(); return [isNow(p) ? d0 : +$(`#${p}Day`).value, isNow(p) ? h0 : +$(`#${p}Hour`).value]; }

/* ---------- Onglet Trafic ---------- */
function drawTrafic() {
  const [d, h] = selDH('t'), live = isNow('t');
  const rows = AX.map(a => ({a, s: state(a, d, h, live)})).sort((x, y) => y.s.v - x.s.v);
  $('#axlist').innerHTML = rows.map(({a, s}) => `<li><button type="button" data-ax="${a.id}"><span class="bar l${lvl(s.v)}"></span><span class="t"><b>${esc(a.nom)}</b><small>${esc(a.zone)} · ${SRC[s.src][1]}</small></span><span class="v">${fmtMin(travel(a, s.v))}<small>${LN[lvl(s.v)]}</small></span></button></li>`).join('');
  paintAxes();
}

/* ---------- Itinéraires ---------- */
const OD = {from: null, to: null};
function setOD(k, p) {
  OD[k] = p; $('#' + k).value = p ? p.label : '';
  odL.clearLayers();
  ['from', 'to'].forEach(x => { if (OD[x]) L.marker([OD[x].lat, OD[x].lng], {icon: L.divIcon({className: '', html: `<div class="mk ${x === 'to' ? 'b' : ''}"></div>`, iconSize: [18, 18], iconAnchor: [9, 9]}), zIndexOffset: 900}).addTo(odL); });
}
let sugT;
function suggest(k) {
  const q = $('#' + k).value.trim(), box = $('#sug-' + k);
  if (q.length < 2) { box.hidden = true; return; }
  const loc = NODES.filter(n => n[0].toLowerCase().includes(q.toLowerCase())).map(n => ({label: n[0], sub: 'Douala', lat: n[1], lng: n[2]}));
  const show = l => { box._l = l; box.innerHTML = l.length ? l.map((r, i) => `<button type="button" data-s="${k}:${i}">${esc(r.label)}<small>${esc(r.sub)}</small></button>`).join('') : '<div style="padding:10px;color:#5d6b7a">Aucun lieu trouvé</div>'; box.hidden = false; };
  show(loc);
  clearTimeout(sugT);
  sugT = setTimeout(() => fetch(`${CFG.nominatim}/search?format=json&limit=6&accept-language=fr&viewbox=9.55,4.20,9.95,3.90&bounded=1&q=${encodeURIComponent(q)}`)
    .then(r => r.json()).then(j => { if ($('#' + k).value.trim() !== q) return; show(loc.concat(j.map(o => ({label: o.display_name.split(',')[0], sub: o.display_name.split(',').slice(1, 3).join(',').trim(), lat: +o.lat, lng: +o.lon})))); }).catch(() => {}), 350);
}
const MANEUVER = {depart: 'Partir', arrive: 'Arrivée', turn: 'Tourner', 'new name': 'Continuer', merge: 'S\'insérer', 'on ramp': 'Prendre la bretelle', 'off ramp': 'Sortir', fork: 'À la fourche, prendre', 'end of road': 'Au bout de la route, tourner', continue: 'Continuer', roundabout: 'Au rond-point, prendre la sortie', rotary: 'Au rond-point, prendre la sortie', 'roundabout turn': 'Au rond-point, tourner', notification: 'Continuer'};
const MOD = {left: 'à gauche', right: 'à droite', 'slight left': 'légèrement à gauche', 'slight right': 'légèrement à droite', 'sharp left': 'franchement à gauche', 'sharp right': 'franchement à droite', straight: 'tout droit', uturn: 'en faisant demi-tour'};
function stepText(s) {
  const m = s.maneuver, base = MANEUVER[m.type] || 'Continuer', road = s.name ? ` sur ${s.name}` : '';
  if (m.type === 'arrive') return 'Arrivée à destination';
  if (m.type === 'roundabout' || m.type === 'rotary') return `${base} ${m.exit || ''}${road}`.trim();
  if (m.type === 'depart') return `Partir${road}`;
  return `${base} ${MOD[m.modifier] || ''}${road}`.replace(/\s+/g, ' ').trim();
}
function routeCongestion(coords, d, h, live) {
  const step = Math.max(1, Math.floor(coords.length / 120)); let n = 0, m = 0, sum = 0;
  for (let i = 0; i < coords.length; i += step) {
    n++; const p = coords[i]; let best = null;
    AX.forEach(a => { const r = locate(p, a.geo); if (r.d < 90 && (!best || r.d < best.d)) best = {d: r.d, a}; });
    if (best) { m++; sum += state(best.a, d, h, live).v; }
  }
  const city = avg(AX.map(a => state(a, d, h, live).v));
  const share = n ? m / n : 0, matched = m ? sum / m : city;
  return {I: share * matched + (1 - share) * city * .6, share};
}
async function calcRoute() {
  if (!OD.from || !OD.to) return toast('Choisissez un départ et une arrivée.');
  const [d, h] = selDH('r'), live = isNow('r');
  $('#routes').innerHTML = '<div class="empty">Calcul de l\'itinéraire…</div>';
  let routes = [];
  try {
    const j = await fetch(`${CFG.osrm}/route/v1/driving/${OD.from.lng},${OD.from.lat};${OD.to.lng},${OD.to.lat}?alternatives=3&overview=full&geometries=geojson&steps=true`).then(r => r.json());
    routes = (j.routes || []).slice(0, 3).map(r => ({geo: r.geometry.coordinates.map(c => [c[1], c[0]]), km: r.distance, base: r.duration / 60, steps: r.legs[0].steps}));
  } catch (e) { routes = []; }
  if (!routes.length) {
    const dist = hav([OD.from.lat, OD.from.lng], [OD.to.lat, OD.to.lng]) * 1.35;
    routes = [{geo: [[OD.from.lat, OD.from.lng], [OD.to.lat, OD.to.lng]], km: dist, base: dist / 1000 / 30 * 60, steps: [], approx: true}];
  }
  routes.forEach(r => { const c = routeCongestion(r.geo, d, h, live); r.I = c.I; r.share = c.share; r.est = r.base * (1 + c.I / 60);
    const names = {}; r.steps.forEach(s => { if (s.name) names[s.name] = (names[s.name] || 0) + s.distance; });
    r.via = Object.keys(names).sort((a, b) => names[b] - names[a]).slice(0, 2); });
  const best = Math.min(...routes.map(r => r.est));
  S.route = routes; S.sel = routes.findIndex(r => r.est === best);
  drawRoutes(); fitView(L.latLngBounds(routes.flatMap(r => r.geo)));
  logAction('Calcul d\'itinéraire');
}
function drawRoutes() {
  routeL.clearLayers();
  const R0 = S.route; if (!R0) return;
  R0.forEach((r, i) => { if (i !== S.sel) L.polyline(r.geo, {color: '#8a97a6', weight: 6, opacity: .75}).on('click', () => { S.sel = i; drawRoutes(); }).addTo(routeL); });
  const s = R0[S.sel];
  L.polyline(s.geo, {color: '#fff', weight: 11, opacity: 1, interactive: false}).addTo(routeL);
  L.polyline(s.geo, {color: '#0070c0', weight: 7, opacity: 1}).addTo(routeL);
  const best = Math.min(...R0.map(r => r.est));
  $('#routes').innerHTML = R0.map((r, i) => `<div class="rcard ${i === S.sel ? 'on' : ''}" data-r="${i}">
    <div class="rtop"><span class="rtime t${lvl(r.I)}">${fmtMin(r.est)}</span>${r.est === best && R0.length > 1 ? '<span class="badge">Le plus rapide</span>' : ''}</div>
    <div class="rmeta">${fmtKm(r.km)} · ${fmtMin(r.base)} sans trafic${r.via.length ? ' · via ' + esc(r.via.join(', ')) : ''}</div>
    <div class="rtop">${pill(r.I)}<span class="rmeta">${r.approx ? 'Tracé approximatif' : Math.round(r.share * 100) + ' % sur axes suivis'}</span></div>
    ${i === S.sel && r.steps.length ? `<button class="linkbtn" type="button" data-steps="${i}">Voir les ${r.steps.length} étapes</button><ol class="steps" id="steps${i}" hidden>${r.steps.map(st => `<li>${esc(stepText(st))}<span>${st.distance >= 1000 ? fmtKm(st.distance) : Math.round(st.distance) + ' m'}</span></li>`).join('')}</ol>` : ''}
  </div>`).join('');
}

/* ---------- Signalements ---------- */
function drawSignalTab() {
  $('#sigGuest').hidden = !!S.user; $('#sigForm').hidden = !S.user;
  $('#sigTypes').innerHTML = Object.entries(RTYPES).map(([k, t]) => `<button type="button" data-st="${k}" class="${k === S.sigType ? 'on' : ''}">${ic(t[1])}${t[0]}</button>`).join('');
  $('#pickHint').classList.toggle('ok', !!S.pick);
  $('#pickHint span').textContent = S.pick ? 'Point placé. Touchez la carte pour le déplacer.' : 'Touchez la carte pour placer le point';
  $('#mySig').innerHTML = S.mine.length ? S.mine.map(r => `<li><span>${(RTYPES[r.type] || [r.type])[0]} · ${fmtDate(r.created_at)}</span><b class="${r.status === 'valide' ? 'p1' : r.status === 'rejete' ? 'p4' : 'p2'}">${{en_attente: 'En attente', valide: 'Publié', rejete: 'Rejeté'}[r.status]}</b></li>`).join('') : '<li><span>Aucun signalement envoyé</span></li>';
}
function setPick(ll) {
  S.pick = ll; if (pickL) pickL.remove();
  pickL = L.marker(ll, {icon: L.divIcon({className: '', html: `<div class="rp" style="background:${RTYPES[S.sigType][2]}">${ic(RTYPES[S.sigType][1])}</div>`, iconSize: [30, 30], iconAnchor: [15, 15]}), zIndexOffset: 950}).addTo(map);
  drawSignalTab();
}
async function loadMine() { if (!S.user) { S.mine = []; return; } const {data} = await sb.from('reports').select('*').eq('user_id', S.user.id).order('created_at', {ascending: false}).limit(10); S.mine = data || []; }
function nearestAxis(ll, max) { let b = null; AX.forEach(a => { const r = locate(ll, a.geo); if (r.d < max && (!b || r.d < b.d)) b = {d: r.d, a, s: r.s}; }); return b; }

function onMapClick(e) {
  const ll = [e.latlng.lat, e.latlng.lng];
  if (S.tab === 'signal' && S.user) return setPick(ll);
  if (S.tab === 'route') {
    const p = {label: `${ll[0].toFixed(5)}, ${ll[1].toFixed(5)}`, lat: ll[0], lng: ll[1]};
    if (!OD.from) setOD('from', p); else if (!OD.to) { setOD('to', p); calcRoute(); }
  }
}

/* ---------- Collecte GPS ---------- */
const REC = {on: false, pts: [], t0: 0, dist: 0, watch: null, timer: null};
function startRec() {
  if (!S.user) { openAuth('login'); return toast('Connectez-vous pour enregistrer vos trajets.'); }
  if (!navigator.geolocation) return toast('La géolocalisation n\'est pas disponible sur cet appareil.');
  Object.assign(REC, {on: true, pts: [], t0: Date.now(), dist: 0});
  $('#recBtn').hidden = true; $('#recBar').hidden = false;
  if (recL) recL.remove(); recL = L.polyline([], {color: '#d42f2f', weight: 5}).addTo(map);
  REC.watch = navigator.geolocation.watchPosition(p => {
    if (p.coords.accuracy > 60) return;
    const pt = [p.coords.latitude, p.coords.longitude, Date.now() - REC.t0], last = REC.pts[REC.pts.length - 1];
    if (last) { const dd = hav(last, pt); if (dd < 5) return; REC.dist += dd; $('#recSpeed').textContent = Math.round(dd / Math.max(1, (pt[2] - last[2]) / 1000) * 3.6); }
    REC.pts.push(pt); recL.addLatLng([pt[0], pt[1]]);
    if (REC.pts.length === 1) map.setView([pt[0], pt[1]], 15);
  }, () => toast('Signal GPS indisponible : autorisez la localisation.'), {enableHighAccuracy: true, maximumAge: 2000, timeout: 20000});
  REC.timer = setInterval(() => { const s = Math.floor((Date.now() - REC.t0) / 1000); $('#recTime').textContent = `${String(Math.floor(s / 60)).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`; $('#recDist').textContent = fmtKm(REC.dist); }, 1000);
}
// Découpe la trace sur chaque axe suivi et en déduit un temps de parcours
function measureAxes(pts, t0) {
  const out = [];
  AX.forEach(a => {
    let run = [], bestRun = [];
    pts.forEach(p => { const r = locate(p, a.geo); if (r.d <= 60) run.push({s: r.s, t: p[2]}); else { if (run.length > bestRun.length) bestRun = run; run = []; } });
    if (run.length > bestRun.length) bestRun = run;
    if (bestRun.length < 3) return;
    const first = bestRun[0], last = bestRun[bestRun.length - 1], cov = Math.abs(last.s - first.s), dt = (last.t - first.t) / 1000;
    if (cov < Math.max(300, .35 * a.len) || dt < 20) return;
    const v = cov / dt, full = a.len / v / 60;
    out.push({axe_id: a.id, observed_at: new Date(t0 + last.t).toISOString(), duree_min: +full.toFixed(1), vitesse_kmh: +(v * 3.6).toFixed(1), indice: Math.round(clamp(45 * (full / a.temps_fluide_min - 1))), source: 'gps'});
  });
  return out;
}
async function stopRec() {
  navigator.geolocation.clearWatch(REC.watch); clearInterval(REC.timer);
  REC.on = false; $('#recBar').hidden = true; $('#recBtn').hidden = false;
  if (REC.pts.length < 3 || REC.dist < 200) { toast('Trajet trop court : rien n\'a été enregistré.'); if (recL) recL.remove(); return; }
  const {data: trip, error} = await sb.from('trips').insert({mode: $('#recMode').value, started_at: new Date(REC.t0).toISOString(), ended_at: new Date().toISOString(), distance_m: Math.round(REC.dist), points: REC.pts.map(p => [+p[0].toFixed(6), +p[1].toFixed(6), p[2]])}).select('id').single();
  if (error) return toast('Échec de l\'enregistrement : ' + error.message);
  const obs = measureAxes(REC.pts, REC.t0).map(o => ({...o, trip_id: trip.id}));
  if (obs.length) await sb.from('observations').insert(obs);
  await logAction(`Trajet GPS enregistré (${fmtKm(REC.dist)}, ${obs.length} axe(s) mesuré(s))`);
  toast(`Trajet enregistré : ${fmtKm(REC.dist)}, ${obs.length} axe${obs.length > 1 ? 's' : ''} mesuré${obs.length > 1 ? 's' : ''}. Merci !`);
  await loadObs(); drawTrafic();
}

/* ---------- Graphiques ---------- */
function lineChart(vals, now) {
  const W = 640, H = 220, L0 = 32, Rr = 10, T = 10, B = 24, x = i => L0 + i * (W - L0 - Rr) / 23, y = v => T + (100 - v) * (H - T - B) / 100;
  let s = `<svg class="chart" viewBox="0 0 ${W} ${H}" role="img" aria-label="Indice par heure">`;
  [0, 25, 50, 75, 100].forEach(v => { s += `<line class="g" x1="${L0}" x2="${W - Rr}" y1="${y(v)}" y2="${y(v)}"/><text x="${L0 - 6}" y="${y(v) + 4}" text-anchor="end">${v}</text>`; });
  for (let i = 0; i < 24; i += 3) s += `<text x="${x(i)}" y="${H - 6}" text-anchor="middle">${i} h</text>`;
  const p = vals.map((v, i) => x(i).toFixed(1) + ',' + y(v).toFixed(1)).join(' ');
  s += `<polygon class="ar" points="${x(0)},${y(0)} ${p} ${x(23)},${y(0)}"/><polyline class="ln" points="${p}"/>`;
  if (now != null) s += `<line class="now" x1="${x(now)}" x2="${x(now)}" y1="${T}" y2="${y(0)}"/>`;
  return s + '</svg>';
}
function barChart(labels, vals, level) {
  const W = 640, H = 220, L0 = 32, Rr = 10, T = 16, B = 24, bw = (W - L0 - Rr) / vals.length, y = v => T + (100 - v) * (H - T - B) / 100;
  let s = `<svg class="chart" viewBox="0 0 ${W} ${H}" role="img" aria-label="Diagramme">`;
  [0, 25, 50, 75, 100].forEach(v => { s += `<line class="g" x1="${L0}" x2="${W - Rr}" y1="${y(v)}" y2="${y(v)}"/><text x="${L0 - 6}" y="${y(v) + 4}" text-anchor="end">${v}</text>`; });
  vals.forEach((v, i) => { const cx = L0 + i * bw + bw / 2, w = Math.min(46, bw * .68);
    s += `<rect class="${level ? 'f' + lvl(v) : 'bx'}" x="${cx - w / 2}" y="${y(v)}" width="${w}" height="${y(0) - y(v)}" rx="3"><title>${esc(labels[i])} : ${Math.round(v)}</title></rect><text x="${cx}" y="${H - 6}" text-anchor="middle">${esc(labels[i])}</text>`;
    if (!level) s += `<text x="${cx}" y="${y(v) - 5}" text-anchor="middle">${Math.round(v)}</text>`; });
  return s + '</svg>';
}

/* ---------- Tableau de bord ---------- */
async function drawTableau() {
  const d = +$('#dDay').value, [d0, h0] = nowDH(), today = d === d0, h = today ? h0 : 8;
  const {data} = await sb.rpc('public_stats'); const st = (data && data[0]) || {};
  const real = S.obs.filter(o => o.d === d).length;
  const k = (i, l, v) => `<div class="kpi"><span class="chip">${ic(i)}</span><div><span>${l}</span><b>${v}</b></div></div>`;
  $('#kpis').innerHTML = k('db', 'Mesures GPS', st.observations_gps ?? 0) + k('route', 'Trajets enregistrés', st.trajets ?? 0) + k('users', 'Contributeurs', st.contributeurs ?? 0) + k('alert', 'Signalements publiés', st.signalements_valides ?? 0) + k('clock', 'En attente', st.signalements_attente ?? 0);
  $('#dSrc').className = 'src ' + (real ? 'hist' : ''); $('#dSrc').textContent = real ? `${real} mesure${real > 1 ? 's' : ''} ce jour-là, complété par le modèle` : 'Aucune mesure ce jour-là : modèle de référence';
  const hv = Array.from({length: 24}, (_, x) => avg(AX.map(a => state(a, d, x, false).v)));
  $('#dHour').innerHTML = lineChart(hv, today ? h0 : null);
  const zn = Object.values(ZONES); $('#dZone').innerHTML = barChart(zn.map(z => z.replace('Deïdo–Bépanda', 'Deïdo-Bép.')), zn.map(z => { const ids = AX.filter(a => a.zone === z); let s = 0; for (let x = 6; x <= 21; x++) s += avg(ids.map(a => state(a, d, x, false).v)); return s / 16; }));
  $('#dAxes').innerHTML = AX.map(a => { const s = state(a, d, h, today); return `<tr><td>${esc(a.nom)}</td><td>${esc(a.zone)}</td><td>${pill(s.v)}</td><td>${Math.round(s.v)}</td><td>${fmtMin(travel(a, s.v))}</td><td>${srcTag(s.src)}</td></tr>`; }).join('');
}
function exportCSV() {
  const rows = ['date;axe;zone;temps_parcours_min;vitesse_kmh;indice;niveau;source'];
  S.obs.forEach(o => { const a = AX.find(x => x.id === o.axe_id); rows.push([new Date(o.observed_at).toLocaleString('fr-FR'), a.nom, a.zone, o.duree_min, o.vitesse_kmh ?? '', o.indice, LN[lvl(o.indice)], o.source].join(';')); });
  if (rows.length === 1) return toast('Aucune mesure enregistrée pour l\'instant.');
  const u = URL.createObjectURL(new Blob(['﻿' + rows.join('\r\n')], {type: 'text/csv;charset=utf-8'})), l = document.createElement('a');
  l.href = u; l.download = 'douala-flow-mesures.csv'; document.body.appendChild(l); l.click(); l.remove(); setTimeout(() => URL.revokeObjectURL(u), 1000);
}

/* ---------- Prévisions ---------- */
function drawPrev() {
  const a = AX.find(x => x.id === +$('#pAxis').value), d = +$('#pDay').value, hs = Array.from({length: 18}, (_, i) => i + 5);
  const st = hs.map(h => state(a, d, h, false)), vals = st.map(s => s.v), nReal = st.filter(s => s.src === 'hist').length;
  const wins = []; let s0 = -1;
  vals.forEach((v, k) => { if (v >= 55 && s0 < 0) s0 = k; if (s0 >= 0 && (v < 55 || k === vals.length - 1)) { wins.push(`${hs[s0]} h – ${(v >= 55 ? hs[k] + 1 : hs[k])} h`); s0 = -1; } });
  $('#pText').textContent = wins.length ? `${a.nom} : trafic dense probable ${wins.join(' et ')}` : `${a.nom} : pas de créneau dense attendu`;
  $('#pChart').innerHTML = barChart(hs.map(String), vals, true);
  $('#pSrc').className = 'src ' + (nReal ? 'hist' : ''); $('#pSrc').textContent = nReal ? `${nReal} créneau${nReal > 1 ? 'x' : ''} sur 18 fondé${nReal > 1 ? 's' : ''} sur des mesures` : 'Modèle de référence (pas encore de mesures)';
  $('#pTable').innerHTML = AX.map(x => { let b = 0, bv = -1; for (let h = 5; h <= 22; h++) { const v = state(x, d, h, false).v; if (v > bv) { bv = v; b = h; } } return {x, b, bv}; }).sort((p, q) => q.bv - p.bv)
    .map(o => `<tr><td>${esc(o.x.nom)}</td><td>${o.b} h – ${o.b + 1} h</td><td>${pill(o.bv)}</td><td>${fmtMin(travel(o.x, o.bv))}</td></tr>`).join('');
}

/* ---------- Administration ---------- */
async function drawAdmin() {
  if (role() !== 'admin') return;
  const [{data: reps}, {data: users}, {data: logs}] = await Promise.all([
    sb.from('reports').select('*').order('created_at', {ascending: false}).limit(100), sb.rpc('admin_list_users'), sb.from('logs').select('*').order('created_at', {ascending: false}).limit(40)]);
  const pend = (reps || []).filter(r => r.status === 'en_attente').length; $('#aPend').textContent = `${pend} en attente`;
  $('#aReports').innerHTML = (reps || []).map(r => `<tr><td>${fmtDate(r.created_at)}</td><td>${(RTYPES[r.type] || [r.type])[0]}</td><td>${esc((AX.find(a => a.id === r.axe_id) || {}).nom || '—')}</td><td>${esc(r.description || '—')}</td><td>${{en_attente: 'En attente', valide: 'Publié', rejete: 'Rejeté'}[r.status]}</td><td style="white-space:nowrap">${r.status === 'en_attente' ? `<button class="btn sm" type="button" data-mod="valide" data-id="${r.id}">Valider</button> <button class="btn ghost sm" type="button" data-mod="rejete" data-id="${r.id}">Rejeter</button>` : ''}</td></tr>`).join('') || '<tr><td colspan="6">Aucun signalement</td></tr>';
  $('#aUsers').innerHTML = (users || []).map(u => `<tr><td>${esc(u.nom)}</td><td>${esc(u.email)}</td><td><select data-uid="${u.id}" ${u.id === S.user.id ? 'disabled' : ''}>${['usager', 'analyste', 'admin'].map(r => `<option value="${r}" ${r === u.role ? 'selected' : ''}>${{usager: 'Usager', analyste: 'Analyste', admin: 'Administrateur'}[r]}</option>`).join('')}</select></td></tr>`).join('');
  $('#aLogs').innerHTML = (logs || []).map(l => `<tr><td>${fmtDate(l.created_at)}</td><td>${esc(l.action)}</td></tr>`).join('') || '<tr><td colspan="2">Journal vide</td></tr>';
  $('#gKey').value = S.gkey;
  setNav(pend);
}
async function regeo() {
  toast('Calcul des tracés en cours…'); let ok = 0; const cache = {};
  for (const a of AX) {
    try { const j = await fetch(`${CFG.osrm}/route/v1/driving/${a.noeuds.map(p => p[1] + ',' + p[0]).join(';')}?overview=full&geometries=geojson`).then(r => r.json());
      const g = j.routes[0].geometry.coordinates.map(c => [+c[1].toFixed(6), +c[0].toFixed(6)]);
      const {error} = await sb.from('axes').update({geometrie: g}).eq('id', a.id); if (!error) { a.geo = g; a.len = lineLen(g); cache[a.id] = g; ok++; } } catch (e) {}
    await new Promise(r => setTimeout(r, 300));
  }
  ls.set('dfa_geo3', cache); paintAxes(); toast(`${ok} tracé${ok > 1 ? 's' : ''} sur 10 mis à jour.`); logAction('Recalcul des tracés des axes');
}

/* ---------- Authentification ---------- */
let authMode = 'login';
function openAuth(m) {
  authMode = m; $('#auth').hidden = false; $('#aErr').hidden = true;
  $('#authTitle').textContent = m === 'login' ? 'Connexion' : 'Créer un compte';
  $('#aSubmit').textContent = m === 'login' ? 'Se connecter' : 'Créer mon compte';
  $('#aSwitch').textContent = m === 'login' ? 'Créer un compte' : 'J\'ai déjà un compte';
  $('#nomRow').hidden = m === 'login'; $('#aPass').autocomplete = m === 'login' ? 'current-password' : 'new-password';
  setTimeout(() => $(m === 'login' ? '#aEmail' : '#aNom').focus(), 50);
}
const AUTH_ERR = {'Invalid login credentials': 'Adresse e-mail ou mot de passe incorrect.', 'User already registered': 'Un compte existe déjà avec cette adresse.', 'Email not confirmed': 'Adresse e-mail non confirmée : ouvrez le lien reçu par e-mail.'};
async function submitAuth(email, pass) {
  const err = $('#aErr'); err.hidden = true; $('#aSubmit').disabled = true;
  try {
    if (authMode === 'login') {
      const {error} = await sb.auth.signInWithPassword({email, password: pass}); if (error) throw error;
    } else {
      const nom = $('#aNom').value.trim(); if (nom.length < 2) throw new Error('Indiquez votre nom.');
      const {data, error} = await sb.auth.signUp({email, password: pass, options: {data: {nom}}}); if (error) throw error;
      if (!data.session) { $('#auth').hidden = true; return toast('Compte créé. Confirmez votre adresse avec le lien reçu par e-mail, puis connectez-vous.'); }
    }
    $('#auth').hidden = true; $('#authForm').reset();
  } catch (e) { err.textContent = AUTH_ERR[e.message] || e.message || 'Une erreur est survenue.'; err.hidden = false; }
  finally { $('#aSubmit').disabled = false; }
}
async function onSession(session) {
  S.user = session ? session.user : null; S.profile = null;
  if (S.user) { const {data} = await sb.from('profiles').select('*').eq('id', S.user.id).single(); S.profile = data || {nom: S.user.email, role: 'usager'}; }
  await loadMine(); drawUser(); setNav(); drawSignalTab();
  if (S.view === 'admin' && role() !== 'admin') go('carte'); else if (S.view === 'admin') drawAdmin();
}
function drawUser() {
  const u = S.profile;
  $('#userBox').innerHTML = u ? `<span class="uname">${esc(u.nom)}<small>${{usager: 'Usager', analyste: 'Analyste', admin: 'Administrateur'}[u.role]}</small></span><span class="avatar">${esc((u.nom || '?').trim().charAt(0).toUpperCase())}</span><button class="icb" type="button" id="logout" title="Se déconnecter" style="background:transparent;border-color:rgba(255,255,255,.3);color:#fff">${ic('logout')}</button>`
    : `<button class="btn sm onnavy" type="button" data-auth="login">Connexion</button><button class="btn sm" type="button" data-auth="signup">Créer un compte</button>`;
}

/* ---------- Navigation ---------- */
const VIEWS = [['carte', 'Carte', 'map'], ['tableau', 'Tableau de bord', 'grid'], ['previsions', 'Prévisions', 'trend'], ['admin', 'Administration', 'shield']];
function setNav(pend) {
  $('#nav').innerHTML = VIEWS.filter(v => v[0] !== 'admin' || role() === 'admin').map(v => `<a href="#${v[0]}" class="${v[0] === S.view ? 'on' : ''}">${ic(v[2])}<span class="lbl">${v[1]}</span>${v[0] === 'admin' && pend ? `<span class="cnt">${pend}</span>` : ''}</a>`).join('');
}
function go(v) {
  if (!VIEWS.some(x => x[0] === v) || (v === 'admin' && role() !== 'admin')) v = 'carte';
  S.view = v; VIEWS.forEach(x => { $('#v-' + x[0]).hidden = x[0] !== v; }); setNav();
  try { history.replaceState(null, '', '#' + v); } catch (e) {}
  if (v === 'carte') setTimeout(() => map.invalidateSize(), 50);
  if (v === 'tableau') drawTableau(); if (v === 'previsions') drawPrev(); if (v === 'admin') drawAdmin();
}
function setTab(t) {
  S.tab = t; $$('.seg button').forEach(b => b.classList.toggle('on', b.dataset.pt === t));
  ['route', 'trafic', 'signal'].forEach(x => { $('#pt-' + x).hidden = x !== t; });
  if (t === 'trafic') drawTrafic(); if (t === 'signal') drawSignalTab();
}

/* ---------- Événements ---------- */
function bind() {
  document.addEventListener('click', async e => {
    const t = e.target;
    const nav = t.closest('a[href^="#"]'); if (nav) { e.preventDefault(); return go(nav.getAttribute('href').slice(1)); }
    const au = t.closest('[data-auth]'); if (au) return openAuth(au.dataset.auth);
    if (t.closest('[data-close]') || t.id === 'auth') { $('#auth').hidden = true; return; }
    if (t.closest('#logout')) { await logAction('Déconnexion'); await sb.auth.signOut(); return toast('Vous êtes déconnecté.'); }
    const dm = t.closest('[data-demo]'); if (dm) { authMode = 'login'; return submitAuth(`${dm.dataset.demo}@douala-flow.demo`, 'demo1234'); }
    const pt = t.closest('[data-pt]'); if (pt) return setTab(pt.dataset.pt);
    const lb = t.closest('[data-l]'); if (lb) return setBase(lb.dataset.l);
    const ax = t.closest('[data-ax]'); if (ax) { const i = AX.findIndex(a => a.id === +ax.dataset.ax); fitView(L.latLngBounds(AX[i].geo)); return axisPopup(i); }
    const sg = t.closest('[data-s]'); if (sg) { const [k, i] = sg.dataset.s.split(':'); const box = $('#sug-' + k); setOD(k, box._l[+i]); box.hidden = true; map.setView([OD[k].lat, OD[k].lng], 14); if (OD.from && OD.to) calcRoute(); return; }
    if (!t.closest('.ac')) $$('.sug').forEach(b => { b.hidden = true; });
    const rc = t.closest('[data-steps]'); if (rc) { const ol = $('#steps' + rc.dataset.steps); ol.hidden = !ol.hidden; rc.textContent = ol.hidden ? `Voir les ${ol.children.length} étapes` : 'Masquer les étapes'; return; }
    const rr = t.closest('[data-r]'); if (rr && +rr.dataset.r !== S.sel) { S.sel = +rr.dataset.r; return drawRoutes(); }
    const ty = t.closest('[data-st]'); if (ty) { S.sigType = ty.dataset.st; if (S.pick) setPick(S.pick); else drawSignalTab(); return; }
    const md = t.closest('[data-mod]'); if (md) { const {error} = await sb.from('reports').update({status: md.dataset.mod, moderated_by: S.user.id}).eq('id', +md.dataset.id); if (error) return toast(error.message); await logAction(`${md.dataset.mod === 'valide' ? 'Validation' : 'Rejet'} du signalement n° ${md.dataset.id}`); await loadReports(); paintReports(); toast(md.dataset.mod === 'valide' ? 'Signalement publié sur la carte.' : 'Signalement rejeté.'); return drawAdmin(); }
  });
  $('#from').addEventListener('input', () => { OD.from = null; suggest('from'); });
  $('#to').addEventListener('input', () => { OD.to = null; suggest('to'); });
  $('#useMe').addEventListener('click', () => locateMe(ll => { setOD('from', {label: 'Ma position', lat: ll[0], lng: ll[1]}); map.setView(ll, 14); if (OD.to) calcRoute(); }));
  $('#swap').addEventListener('click', () => { const f = OD.from; setOD('from', OD.to); setOD('to', f); if (OD.from && OD.to) calcRoute(); });
  $('#go').addEventListener('click', calcRoute);
  ['rDay', 'rHour'].forEach(id => $('#' + id).addEventListener('change', () => { if (S.route) calcRoute(); }));
  ['tDay', 'tHour'].forEach(id => $('#' + id).addEventListener('change', drawTrafic));
  $('#tNow').addEventListener('click', () => { fillDH('t'); drawTrafic(); });
  $('#locate').addEventListener('click', () => locateMe());
  $('#sigMe').addEventListener('click', () => locateMe(ll => { setPick(ll); map.setView(ll, 16); }));
  $('#sigForm').addEventListener('submit', async e => {
    e.preventDefault(); if (!S.pick) return toast('Placez d\'abord le point sur la carte.');
    const na = nearestAxis(S.pick, 300);
    const {error} = await sb.from('reports').insert({type: S.sigType, lat: S.pick[0], lng: S.pick[1], axe_id: na ? na.a.id : null, description: $('#sigDesc').value.trim() || null});
    if (error) return toast('Envoi impossible : ' + error.message);
    await logAction('Envoi d\'un signalement'); $('#sigDesc').value = ''; S.pick = null; if (pickL) pickL.remove();
    await loadMine(); drawSignalTab(); toast('Signalement envoyé. Il sera publié après validation.');
  });
  $('#recBtn').addEventListener('click', startRec); $('#recStop').addEventListener('click', stopRec);
  $('#authForm').addEventListener('submit', e => { e.preventDefault(); submitAuth($('#aEmail').value.trim(), $('#aPass').value); });
  $('#aSwitch').addEventListener('click', e => { e.preventDefault(); openAuth(authMode === 'login' ? 'signup' : 'login'); });
  document.addEventListener('keydown', e => { if (e.key === 'Escape') $('#auth').hidden = true; });
  $('#dDay').addEventListener('change', drawTableau); $('#csv').addEventListener('click', exportCSV);
  $('#pAxis').addEventListener('change', drawPrev); $('#pDay').addEventListener('change', drawPrev);
  $('#aUsers').addEventListener('change', async e => { const s = e.target.closest('[data-uid]'); if (!s) return; const {error} = await sb.from('profiles').update({role: s.value}).eq('id', s.dataset.uid); if (error) return toast(error.message); await logAction('Changement de rôle d\'un utilisateur'); toast('Rôle mis à jour.'); });
  $('#obsForm').addEventListener('submit', async e => { e.preventDefault(); const a = AX.find(x => x.id === +$('#oAxis').value), dur = +$('#oDur').value;
    const {error} = await sb.from('observations').insert({axe_id: a.id, duree_min: dur, vitesse_kmh: +(a.len / 1000 / (dur / 60)).toFixed(1), indice: Math.round(clamp(45 * (dur / a.temps_fluide_min - 1))), source: 'terrain'});
    if (error) return toast(error.message); await logAction(`Observation de terrain : ${a.nom}`); await loadObs(); toast('Observation enregistrée.'); });
  $('#setForm').addEventListener('submit', async e => { e.preventDefault(); const v = $('#gKey').value.trim(); const {error} = await sb.from('settings').update({value: v}).eq('key', 'google_maps_key'); if (error) return toast(error.message); S.gkey = v; await logAction('Mise à jour de la clé Google Maps'); toast('Paramètres enregistrés.'); });
  $('#regeo').addEventListener('click', regeo);
  window.addEventListener('hashchange', () => { const v = location.hash.slice(1); if (v && v !== S.view) go(v); });
}

/* ---------- Démarrage ---------- */
async function start() {
  ['r', 't'].forEach(fillDH);
  ['dDay', 'pDay'].forEach(id => { $('#' + id).innerHTML = DAYS.map((d, i) => `<option value="${i}">${d}</option>`).join(''); $('#' + id).value = nowDH()[0]; });
  try { await loadAxes(); } catch (e) { toast('Connexion à la base impossible. Vérifiez votre connexion internet.'); return; }
  const opts = AX.map(a => `<option value="${a.id}">${esc(a.nom)}</option>`).join(''); $('#pAxis').innerHTML = opts; $('#oAxis').innerHTML = opts; $('#pAxis').value = 9;
  initMap(); bind();
  await Promise.all([loadObs(), loadReports(), loadSettings()]);
  paintReports(); drawTrafic();
  const {data} = await sb.auth.getSession(); await onSession(data.session);
  sb.auth.onAuthStateChange((_e, session) => { setTimeout(() => onSession(session), 0); });
  go((location.hash || '#carte').slice(1));
  if (AX.some(a => !a.geometrie) && !ls.get('dfa_geo3')) bgGeo();
  setInterval(async () => { await Promise.all([loadObs(), loadReports()]); paintReports(); if (S.tab === 'trafic') drawTrafic(); else paintAxes(); }, 60000);
}
// Tracés routiers calculés côté client si la base n'en contient pas encore
async function bgGeo() {
  const cache = {};
  for (const a of AX) { try { const j = await fetch(`${CFG.osrm}/route/v1/driving/${a.noeuds.map(p => p[1] + ',' + p[0]).join(';')}?overview=full&geometries=geojson`).then(r => r.json()); cache[a.id] = j.routes[0].geometry.coordinates.map(c => [c[1], c[0]]); a.geo = cache[a.id]; a.len = lineLen(a.geo); } catch (e) {} await new Promise(r => setTimeout(r, 250)); }
  if (Object.keys(cache).length === AX.length) ls.set('dfa_geo3', cache);
  paintAxes();
}
start();
})();
