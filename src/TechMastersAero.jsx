import React, { useState, useEffect, useRef, useMemo } from 'react';
import {
  Cpu,
  Code2,
  Sparkles,
  Bot,
  QrCode,
  Layers,
  Zap,
  Trophy,
  Users,
  Terminal,
  Palette,
  FileCode,
  Braces,
  ChevronRight,
  Check,
  Copy,
  Download,
  RotateCcw,
  Wifi,
  Globe,
  Eye,
  ShieldCheck,
  CircuitBoard,
  Monitor,
  Power,
  AppWindow
} from 'lucide-react';

// Alias de React.createElement para construir toda la interfaz en JavaScript puro (Cero JSX / Cero HTML estático)
const el = React.createElement;

/**
 * ============================================================================
 * MOTOR DE GENERACIÓN DE CÓDIGO QR PURO EN JAVASCRIPT (SIN LIBRERÍAS EXTERNAS)
 * Implementa el estándar QR Model 2 (Modo Byte, Corrección de Errores ECC L,
 * Aritmética de Campos de Galois GF(256), Polinomios Reed-Solomon y Evaluación
 * de Máscaras) para generar códigos 100% reales y escaneables por celulares.
 * ============================================================================
 */
const QR_ENGINE = (() => {
  const EXP_TABLE = new Uint8Array(512);
  const LOG_TABLE = new Uint8Array(256);
  let x = 1;
  for (let i = 0; i < 255; i++) {
    EXP_TABLE[i] = x;
    LOG_TABLE[x] = i;
    x <<= 1;
    if (x & 0x100) x ^= 0x11d;
  }
  for (let i = 255; i < 512; i++) {
    EXP_TABLE[i] = EXP_TABLE[i - 255];
  }

  const gfMul = (a, b) => {
    if (a === 0 || b === 0) return 0;
    return EXP_TABLE[LOG_TABLE[a] + LOG_TABLE[b]];
  };

  const getGeneratorPoly = (ecCount) => {
    let poly = [1];
    for (let i = 0; i < ecCount; i++) {
      const next = new Array(poly.length + 1).fill(0);
      const factor = EXP_TABLE[i];
      for (let j = 0; j < poly.length; j++) {
        next[j] ^= poly[j];
        next[j + 1] ^= gfMul(poly[j], factor);
      }
      poly = next;
    }
    return poly;
  };

  const computeReedSolomon = (data, ecCount) => {
    const gen = getGeneratorPoly(ecCount);
    const res = new Uint8Array(data.length + ecCount);
    res.set(data);
    for (let i = 0; i < data.length; i++) {
      const coef = res[i];
      if (coef !== 0) {
        for (let j = 0; j < gen.length; j++) {
          res[i + j] ^= gfMul(gen[j], coef);
        }
      }
    }
    return res.slice(data.length);
  };

  const VERSION_SPECS = [
    null,
    { maxBytes: 17, totalData: 19, blocks: [19], ecPerBlock: 7, align: [] },
    { maxBytes: 32, totalData: 34, blocks: [34], ecPerBlock: 10, align: [6, 18] },
    { maxBytes: 53, totalData: 55, blocks: [55], ecPerBlock: 15, align: [6, 22] },
    { maxBytes: 78, totalData: 80, blocks: [80], ecPerBlock: 20, align: [6, 26] },
    { maxBytes: 106, totalData: 108, blocks: [108], ecPerBlock: 26, align: [6, 30] },
    { maxBytes: 134, totalData: 136, blocks: [68, 68], ecPerBlock: 18, align: [6, 34] },
    { maxBytes: 154, totalData: 156, blocks: [78, 78], ecPerBlock: 20, align: [6, 22, 38] },
    { maxBytes: 192, totalData: 194, blocks: [97, 97], ecPerBlock: 24, align: [6, 24, 42] },
    { maxBytes: 230, totalData: 232, blocks: [116, 116], ecPerBlock: 30, align: [6, 26, 46] },
    { maxBytes: 270, totalData: 274, blocks: [68, 68, 69, 69], ecPerBlock: 18, align: [6, 28, 50] }
  ];

  const FORMAT_INFO_L = [
    0x77c4, 0x72f3, 0x7daa, 0x789d,
    0x662f, 0x6318, 0x6c41, 0x6976
  ];

  const VERSION_INFO = {
    7: 0x07c94,
    8: 0x085bc,
    9: 0x09a99,
    10: 0x0a4d3
  };

  const MASK_FNS = [
    (r, c) => (r + c) % 2 === 0,
    (r) => r % 2 === 0,
    (_, c) => c % 3 === 0,
    (r, c) => (r + c) % 3 === 0,
    (r, c) => (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0,
    (r, c) => ((r * c) % 2) + ((r * c) % 3) === 0,
    (r, c) => (((r * c) % 2) + ((r * c) % 3)) % 2 === 0,
    (r, c) => (((r + c) % 2) + ((r * c) % 3)) % 2 === 0
  ];

  const generateMatrix = (text) => {
    const encoder = new TextEncoder();
    let bytes = encoder.encode(text || 'https://techmasters.club');
    if (bytes.length > 270) {
      bytes = bytes.slice(0, 270);
    }

    let version = 1;
    for (let v = 1; v <= 10; v++) {
      if (bytes.length <= VERSION_SPECS[v].maxBytes) {
        version = v;
        break;
      }
    }

    const spec = VERSION_SPECS[version];
    const size = version * 4 + 17;

    const bits = [];
    const pushBits = (val, len) => {
      for (let i = len - 1; i >= 0; i--) {
        bits.push((val >>> i) & 1);
      }
    };

    pushBits(0b0100, 4);
    pushBits(bytes.length, version >= 10 ? 16 : 8);
    for (let i = 0; i < bytes.length; i++) {
      pushBits(bytes[i], 8);
    }

    const capacityBits = spec.totalData * 8;
    const terminatorLen = Math.min(4, capacityBits - bits.length);
    pushBits(0, terminatorLen);

    while (bits.length % 8 !== 0) {
      bits.push(0);
    }

    const padBytes = [0xec, 0x11];
    let padIdx = 0;
    while (bits.length < capacityBits) {
      pushBits(padBytes[padIdx % 2], 8);
      padIdx++;
    }

    const dataCodewords = new Uint8Array(spec.totalData);
    for (let i = 0; i < spec.totalData; i++) {
      let byteVal = 0;
      for (let b = 0; b < 8; b++) {
        byteVal = (byteVal << 1) | bits[i * 8 + b];
      }
      dataCodewords[i] = byteVal;
    }

    const dataBlocks = [];
    const ecBlocks = [];
    let offset = 0;
    for (const blockLen of spec.blocks) {
      const slice = dataCodewords.slice(offset, offset + blockLen);
      dataBlocks.push(slice);
      ecBlocks.push(computeReedSolomon(slice, spec.ecPerBlock));
      offset += blockLen;
    }

    const finalCodewords = [];
    const maxDataBlockLen = Math.max(...spec.blocks);
    for (let i = 0; i < maxDataBlockLen; i++) {
      for (let b = 0; b < dataBlocks.length; b++) {
        if (i < dataBlocks[b].length) {
          finalCodewords.push(dataBlocks[b][i]);
        }
      }
    }
    for (let i = 0; i < spec.ecPerBlock; i++) {
      for (let b = 0; b < ecBlocks.length; b++) {
        finalCodewords.push(ecBlocks[b][i]);
      }
    }

    const streamBits = [];
    for (const cw of finalCodewords) {
      for (let b = 7; b >= 0; b--) {
        streamBits.push((cw >>> b) & 1);
      }
    }

    const baseModules = Array.from({ length: size }, () => new Uint8Array(size));
    const isFunction = Array.from({ length: size }, () => new Uint8Array(size));

    const setFunctionModule = (r, c, val) => {
      if (r >= 0 && r < size && c >= 0 && c < size) {
        baseModules[r][c] = val ? 1 : 0;
        isFunction[r][c] = 1;
      }
    };

    const drawFinder = (row, col) => {
      for (let r = -1; r <= 7; r++) {
        for (let c = -1; c <= 7; c++) {
          const inOuter = r >= 0 && r <= 6 && c >= 0 && c <= 6;
          const inInner = r >= 2 && r <= 4 && c >= 2 && c <= 4;
          const onBorder = r === 0 || r === 6 || c === 0 || c === 6;
          const dark = inOuter && (onBorder || inInner);
          setFunctionModule(row + r, col + c, dark ? 1 : 0);
        }
      }
    };

    drawFinder(0, 0);
    drawFinder(0, size - 7);
    drawFinder(size - 7, 0);

    if (spec.align.length > 0) {
      for (const rCenter of spec.align) {
        for (const cCenter of spec.align) {
          const isTopLeft = rCenter === 6 && cCenter === 6;
          const isTopRight = rCenter === 6 && cCenter === size - 7;
          const isBottomLeft = rCenter === size - 7 && cCenter === 6;
          if (isTopLeft || isTopRight || isBottomLeft) continue;

          for (let r = -2; r <= 2; r++) {
            for (let c = -2; c <= 2; c++) {
              const dark = Math.abs(r) === 2 || Math.abs(c) === 2 || (r === 0 && c === 0);
              setFunctionModule(rCenter + r, cCenter + c, dark ? 1 : 0);
            }
          }
        }
      }
    }

    for (let i = 8; i < size - 8; i++) {
      const dark = i % 2 === 0 ? 1 : 0;
      if (!isFunction[6][i]) setFunctionModule(6, i, dark);
      if (!isFunction[i][6]) setFunctionModule(i, 6, dark);
    }

    setFunctionModule(size - 8, 8, 1);

    for (let i = 0; i < 9; i++) {
      if (!isFunction[8][i]) isFunction[8][i] = 1;
      if (!isFunction[i][8]) isFunction[i][8] = 1;
    }
    for (let i = 0; i < 8; i++) {
      if (!isFunction[8][size - 1 - i]) isFunction[8][size - 1 - i] = 1;
      if (!isFunction[size - 1 - i][8]) isFunction[size - 1 - i][8] = 1;
    }

    if (version >= 7) {
      for (let i = 0; i < 6; i++) {
        for (let j = 0; j < 3; j++) {
          isFunction[i][size - 11 + j] = 1;
          isFunction[size - 11 + j][i] = 1;
        }
      }
    }

    let bitIndex = 0;
    let upward = true;
    for (let right = size - 1; right >= 1; right -= 2) {
      if (right === 6) right = 5;
      for (let vert = 0; vert < size; vert++) {
        const r = upward ? size - 1 - vert : vert;
        for (let lr = 0; lr < 2; lr++) {
          const c = right - lr;
          if (!isFunction[r][c]) {
            const bit = bitIndex < streamBits.length ? streamBits[bitIndex] : 0;
            baseModules[r][c] = bit;
            bitIndex++;
          }
        }
      }
      upward = !upward;
    }

    const applyFormatAndVersion = (grid, maskIdx) => {
      const fmt = FORMAT_INFO_L[maskIdx];
      for (let i = 0; i <= 5; i++) grid[8][i] = (fmt >>> i) & 1;
      grid[8][7] = (fmt >>> 6) & 1;
      grid[8][8] = (fmt >>> 7) & 1;
      grid[7][8] = (fmt >>> 8) & 1;
      for (let i = 9; i < 15; i++) grid[14 - i][8] = (fmt >>> i) & 1;

      for (let i = 0; i < 8; i++) grid[8][size - 1 - i] = (fmt >>> i) & 1;
      for (let i = 8; i < 15; i++) grid[size - 15 + i][8] = (fmt >>> i) & 1;

      if (version >= 7) {
        const vBits = VERSION_INFO[version];
        for (let i = 0; i < 18; i++) {
          const bit = (vBits >>> i) & 1;
          const r = Math.floor(i / 3);
          const c = size - 11 + (i % 3);
          grid[r][c] = bit;
          grid[c][r] = bit;
        }
      }
    };

    let bestMask = 0;
    let bestScore = Infinity;
    let bestGrid = null;

    for (let m = 0; m < 8; m++) {
      const candidate = baseModules.map((row) => new Uint8Array(row));
      const maskFn = MASK_FNS[m];
      for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
          if (!isFunction[r][c] && maskFn(r, c)) {
            candidate[r][c] ^= 1;
          }
        }
      }
      applyFormatAndVersion(candidate, m);

      let darkCount = 0;
      let penalty = 0;
      for (let r = 0; r < size; r++) {
        let runColor = candidate[r][0];
        let runLen = 1;
        for (let c = 0; c < size; c++) {
          if (candidate[r][c]) darkCount++;
          if (c > 0) {
            if (candidate[r][c] === runColor) {
              runLen++;
              if (runLen === 5) penalty += 3;
              else if (runLen > 5) penalty += 1;
            } else {
              runColor = candidate[r][c];
              runLen = 1;
            }
          }
          if (r < size - 1 && c < size - 1) {
            const v = candidate[r][c];
            if (
              v === candidate[r][c + 1] &&
              v === candidate[r + 1][c] &&
              v === candidate[r + 1][c + 1]
            ) {
              penalty += 3;
            }
          }
        }
      }
      const darkPercent = (darkCount * 100) / (size * size);
      penalty += Math.abs(Math.floor(darkPercent / 5) - 10) * 10;

      if (penalty < bestScore) {
        bestScore = penalty;
        bestMask = m;
        bestGrid = candidate;
      }
    }

    return { matrix: bestGrid, size, version, mask: bestMask };
  };

  return { generateMatrix };
})();

/**
 * ============================================================================
 * DATOS DEL CONTENIDO DEL CLUB TECH MASTERS (100% EN ESPAÑOL)
 * ============================================================================
 */
const PROGRAMMING_TOPICS = [
  {
    id: 'python',
    exeName: 'Python_AI.exe',
    name: 'Python',
    badge: 'IA, Datos & Backend',
    statusBar: 'Proceso: Python 3.12 | Tema: Esmeralda Aero',
    accent: '#059669',
    secondary: '#10B981',
    icon: Terminal,
    theme: {
      windowBg:
        'linear-gradient(160deg, rgba(236, 253, 245, 0.90) 0%, rgba(255, 255, 255, 0.85) 55%, rgba(209, 250, 229, 0.84) 100%)',
      ringColor: 'rgba(16, 185, 129, 0.48)',
      hoverRingColor: 'rgba(16, 185, 129, 0.88)',
      shadowColor: 'rgba(5, 150, 105, 0.22)',
      hoverShadowColor: 'rgba(16, 185, 129, 0.36)',
      titlebarGradient:
        'linear-gradient(180deg, rgba(255, 255, 255, 0.94) 0%, rgba(209, 250, 229, 0.84) 49%, rgba(16, 185, 129, 0.32) 50%, rgba(52, 211, 153, 0.24) 100%)',
      iconGradient: 'linear-gradient(180deg, #34D399 0%, #10B981 48%, #059669 100%)',
      buttonGradient: 'linear-gradient(180deg, #34D399 0%, #10B981 48%, #059669 100%)',
      buttonShadow: '0 8px 20px rgba(5, 150, 105, 0.32), inset 0 1px 0 rgba(255, 255, 255, 0.85)',
      headingGradient: 'linear-gradient(180deg, #064E3B 0%, #059669 52%, #10B981 100%)',
      badgeBg: '#D1FAE5',
      badgeText: '#065F46',
      labelColor: '#047857',
      cardTintBg: 'rgba(209, 250, 229, 0.65)',
      statusbarBg: 'linear-gradient(180deg, #ECFDF5 0%, #D1FAE5 100%)',
      statusbarBorder: '#6EE7B7',
      ledColor: '#10B981'
    },
    whatItDoes:
      'Es un lenguaje de programación de alto nivel con sintaxis limpia, clara y potente que permite crear algoritmos inteligentes con pocas líneas de código.',
    whatItIsFor:
      'Sirve para desarrollar Inteligencia Artificial, automatización de tareas, análisis de datos, servidores backend y el cerebro lógico de robots.',
    aiSynergy:
      'En TECH MASTERS combinamos Python con modelos de IA para crear asistentes inteligentes, visión artificial y rutas autónomas.',
    projectExample: 'Clasificador visual inteligente, análisis de sensores y asistente de voz.',
    codeSnippet: [
      '# Control inteligente con IA, datos y automatización en Python',
      'def decidir_ruta_robot(distancia_cm, objeto_detectado):',
      '    if distancia_cm < 18:',
      '        return "ESQUIVAR_OBSTACULO"',
      '    elif objeto_detectado == "META_ESMERALDA":',
      '        return "ACELERAR_HACIA_OBJETIVO"',
      '    return "EXPLORACION_AUTONOMA"'
    ].join('\n')
  },
  {
    id: 'html',
    exeName: 'HTML5_Estructura.exe',
    name: 'HTML',
    badge: 'Estructura Semántica',
    statusBar: 'Proceso: DOM Semántico | Tema: Coral Cristalino',
    accent: '#EA580C',
    secondary: '#F97316',
    icon: FileCode,
    theme: {
      windowBg:
        'linear-gradient(160deg, rgba(255, 247, 237, 0.90) 0%, rgba(255, 255, 255, 0.85) 55%, rgba(255, 237, 213, 0.84) 100%)',
      ringColor: 'rgba(249, 115, 22, 0.48)',
      hoverRingColor: 'rgba(249, 115, 22, 0.88)',
      shadowColor: 'rgba(234, 88, 12, 0.22)',
      hoverShadowColor: 'rgba(249, 115, 22, 0.36)',
      titlebarGradient:
        'linear-gradient(180deg, rgba(255, 255, 255, 0.94) 0%, rgba(255, 237, 213, 0.84) 49%, rgba(249, 115, 22, 0.32) 50%, rgba(251, 146, 60, 0.24) 100%)',
      iconGradient: 'linear-gradient(180deg, #FB923C 0%, #F97316 48%, #EA580C 100%)',
      buttonGradient: 'linear-gradient(180deg, #FB923C 0%, #F97316 48%, #EA580C 100%)',
      buttonShadow: '0 8px 20px rgba(234, 88, 12, 0.32), inset 0 1px 0 rgba(255, 255, 255, 0.85)',
      headingGradient: 'linear-gradient(180deg, #7C2D12 0%, #EA580C 52%, #F97316 100%)',
      badgeBg: '#FFEDD5',
      badgeText: '#9A3412',
      labelColor: '#C2410C',
      cardTintBg: 'rgba(255, 237, 213, 0.65)',
      statusbarBg: 'linear-gradient(180deg, #FFF7ED 0%, #FFEDD5 100%)',
      statusbarBorder: '#FDBA74',
      ledColor: '#F97316'
    },
    whatItDoes:
      'Es el lenguaje de marcado que construye la estructura semántica de las páginas web mediante etiquetas organizadas para encabezados, secciones y multimedia.',
    whatItIsFor:
      'Sirve para dar cimientos sólidos, orden y accesibilidad a cualquier sitio web o aplicación profesional antes de aplicar estilos e interactividad.',
    aiSynergy:
      'Aprendemos arquitectura semántica limpia y cómo motores modernos como React generan el árbol DOM dinámicamente sin páginas estáticas.',
    projectExample: 'Portafolio interactivo de proyectos tecnológicos y bitácora de torneos.',
    codeSnippet: [
      '<!-- Estructura semántica de un módulo web -->',
      '<section class="panel-robotica">',
      '  <h2>Misión Lunar TECH MASTERS</h2>',
      '  <p>Telemetría en tiempo real del rover autónomo.</p>',
      '  <button type="button">Iniciar Secuencia</button>',
      '</section>'
    ].join('\n')
  },
  {
    id: 'javascript',
    exeName: 'JS_Motor.exe',
    name: 'JavaScript',
    badge: 'Motor Interactivo',
    statusBar: 'Proceso: V8 Pure JS | Tema: Dorado Solar',
    accent: '#CA8A04',
    secondary: '#EAB308',
    icon: Braces,
    theme: {
      windowBg:
        'linear-gradient(160deg, rgba(254, 252, 232, 0.92) 0%, rgba(255, 255, 255, 0.86) 55%, rgba(254, 249, 195, 0.86) 100%)',
      ringColor: 'rgba(234, 179, 8, 0.52)',
      hoverRingColor: 'rgba(234, 179, 8, 0.92)',
      shadowColor: 'rgba(202, 138, 4, 0.22)',
      hoverShadowColor: 'rgba(234, 179, 8, 0.38)',
      titlebarGradient:
        'linear-gradient(180deg, rgba(255, 255, 255, 0.95) 0%, rgba(254, 249, 195, 0.86) 49%, rgba(234, 179, 8, 0.34) 50%, rgba(250, 204, 21, 0.26) 100%)',
      iconGradient: 'linear-gradient(180deg, #FACC15 0%, #EAB308 48%, #CA8A04 100%)',
      buttonGradient: 'linear-gradient(180deg, #FACC15 0%, #EAB308 48%, #CA8A04 100%)',
      buttonShadow: '0 8px 20px rgba(202, 138, 4, 0.32), inset 0 1px 0 rgba(255, 255, 255, 0.9)',
      headingGradient: 'linear-gradient(180deg, #713F12 0%, #CA8A04 52%, #EAB308 100%)',
      badgeBg: '#FEF9C3',
      badgeText: '#854D0E',
      labelColor: '#A16207',
      cardTintBg: 'rgba(254, 249, 195, 0.68)',
      statusbarBg: 'linear-gradient(180deg, #FEFCE8 0%, #FEF9C3 100%)',
      statusbarBorder: '#FDE047',
      ledColor: '#EAB308'
    },
    whatItDoes:
      'Es el lenguaje dinámico que dota de interactividad, cálculos matemáticos y lógica en tiempo real a las plataformas web.',
    whatItIsFor:
      'Sirve para crear aplicaciones web reactivas, videojuegos en navegador, motores gráficos, conexión con APIs de IA y paneles de control.',
    aiSynergy:
      'Con JavaScript puro y React los estudiantes construyen aplicaciones completas (como esta misma web) y motores QR sin HTML estático.',
    projectExample: 'Videojuegos web en Canvas y ventanas Aero creadas 100% con React.createElement.',
    codeSnippet: [
      '// Renderizado puro sin JSX ni HTML estático',
      'const crearBotonAero = (texto, alHacerClic) => {',
      '  return React.createElement(',
      '    "button",',
      '    { className: "win-aero-btn", onClick: alHacerClic },',
      '    texto',
      '  );',
      '};'
    ].join('\n')
  },
  {
    id: 'css',
    exeName: 'CSS3_Aero.exe',
    name: 'CSS',
    badge: 'Diseño & Aero UI',
    statusBar: 'Proceso: Aero Compositor | Tema: Zafiro Eléctrico',
    accent: '#0284C7',
    secondary: '#0EA5E9',
    icon: Palette,
    theme: {
      windowBg:
        'linear-gradient(160deg, rgba(240, 249, 255, 0.90) 0%, rgba(255, 255, 255, 0.85) 55%, rgba(224, 242, 254, 0.84) 100%)',
      ringColor: 'rgba(14, 165, 233, 0.48)',
      hoverRingColor: 'rgba(14, 165, 233, 0.88)',
      shadowColor: 'rgba(2, 132, 199, 0.24)',
      hoverShadowColor: 'rgba(14, 165, 233, 0.36)',
      titlebarGradient:
        'linear-gradient(180deg, rgba(255, 255, 255, 0.94) 0%, rgba(224, 242, 254, 0.84) 49%, rgba(14, 165, 233, 0.32) 50%, rgba(56, 189, 248, 0.24) 100%)',
      iconGradient: 'linear-gradient(180deg, #38BDF8 0%, #0EA5E9 48%, #0284C7 100%)',
      buttonGradient: 'linear-gradient(180deg, #38BDF8 0%, #0EA5E9 48%, #0284C7 100%)',
      buttonShadow: '0 8px 20px rgba(2, 132, 199, 0.32), inset 0 1px 0 rgba(255, 255, 255, 0.85)',
      headingGradient: 'linear-gradient(180deg, #0C4A6E 0%, #0284C7 52%, #0EA5E9 100%)',
      badgeBg: '#E0F2FE',
      badgeText: '#075985',
      labelColor: '#0369A1',
      cardTintBg: 'rgba(224, 242, 254, 0.68)',
      statusbarBg: 'linear-gradient(180deg, #F0F9FF 0%, #E0F2FE 100%)',
      statusbarBorder: '#7DD3FC',
      ledColor: '#0EA5E9'
    },
    whatItDoes:
      'Es el lenguaje de diseño visual que controla colores, tipografías luminosas, animaciones fluidas y efectos cristalinos.',
    whatItIsFor:
      'Sirve para transformar estructuras web en interfaces profesionales, 100% responsive para celulares y con estética Frutiger Aero.',
    aiSynergy:
      'Dominamos desenfoques de vidrio (backdrop-filter), destellos hover y layouts adaptables acelerados por GPU.',
    projectExample: 'Sistema de ventanas cristalinas Windows Vista/7 Aero y letras glossy.',
    codeSnippet: [
      '.ventana-windows-aero {',
      '  background: rgba(255, 255, 255, 0.85);',
      '  backdrop-filter: blur(16px) saturate(180%);',
      '  border: 1px solid rgba(14, 165, 233, 0.55);',
      '  box-shadow: 0 18px 45px rgba(2, 132, 199, 0.24);',
      '}'
    ].join('\n')
  }
];

const SPIKE_THEME = {
  windowBg:
    'linear-gradient(160deg, rgba(245, 243, 255, 0.90) 0%, rgba(255, 255, 255, 0.85) 55%, rgba(237, 233, 254, 0.84) 100%)',
  ringColor: 'rgba(139, 92, 246, 0.48)',
  hoverRingColor: 'rgba(139, 92, 246, 0.88)',
  shadowColor: 'rgba(124, 58, 237, 0.24)',
  hoverShadowColor: 'rgba(139, 92, 246, 0.36)',
  titlebarGradient:
    'linear-gradient(180deg, rgba(255, 255, 255, 0.94) 0%, rgba(237, 233, 254, 0.84) 49%, rgba(139, 92, 246, 0.30) 50%, rgba(167, 139, 250, 0.24) 100%)',
  iconGradient: 'linear-gradient(180deg, #A78BFA 0%, #8B5CF6 48%, #7C3AED 100%)',
  buttonGradient: 'linear-gradient(180deg, #A78BFA 0%, #8B5CF6 48%, #7C3AED 100%)',
  buttonShadow: '0 8px 20px rgba(124, 58, 237, 0.32), inset 0 1px 0 rgba(255, 255, 255, 0.85)',
  headingGradient: 'linear-gradient(180deg, #4C1D95 0%, #7C3AED 52%, #8B5CF6 100%)',
  badgeBg: '#EDE9FE',
  badgeText: '#5B21B6',
  labelColor: '#6D28D9',
  cardTintBg: 'rgba(237, 233, 254, 0.65)',
  statusbarBg: 'linear-gradient(180deg, #F5F3FF 0%, #EDE9FE 100%)',
  statusbarBorder: '#C4B5FD',
  ledColor: '#8B5CF6'
};

const ARDUINO_THEME = {
  windowBg:
    'linear-gradient(160deg, rgba(255, 241, 242, 0.90) 0%, rgba(255, 255, 255, 0.85) 55%, rgba(255, 228, 230, 0.84) 100%)',
  ringColor: 'rgba(244, 63, 94, 0.48)',
  hoverRingColor: 'rgba(244, 63, 94, 0.88)',
  shadowColor: 'rgba(225, 29, 72, 0.24)',
  hoverShadowColor: 'rgba(244, 63, 94, 0.36)',
  titlebarGradient:
    'linear-gradient(180deg, rgba(255, 255, 255, 0.94) 0%, rgba(255, 228, 230, 0.84) 49%, rgba(244, 63, 94, 0.30) 50%, rgba(251, 113, 133, 0.24) 100%)',
  iconGradient: 'linear-gradient(180deg, #FB7185 0%, #F43F5E 48%, #E11D48 100%)',
  buttonGradient: 'linear-gradient(180deg, #FB7185 0%, #F43F5E 48%, #E11D48 100%)',
  buttonShadow: '0 8px 20px rgba(225, 29, 72, 0.32), inset 0 1px 0 rgba(255, 255, 255, 0.85)',
  headingGradient: 'linear-gradient(180deg, #881337 0%, #E11D48 52%, #F43F5E 100%)',
  badgeBg: '#FFE4E6',
  badgeText: '#9F1239',
  labelColor: '#BE123C',
  cardTintBg: 'rgba(255, 228, 230, 0.65)',
  statusbarBg: 'linear-gradient(180deg, #FFF1F2 0%, #FFE4E6 100%)',
  statusbarBorder: '#FDA4AF',
  ledColor: '#F43F5E'
};

const SPIKE_PARTS = [
  {
    id: 'hub',
    name: 'Hub Inteligente Programable',
    tag: 'Cerebro Central 5x5',
    description:
      'Unidad central con matriz de luces LED 5x5 programable, giroscopio interno de 6 ejes, conectividad Bluetooth/USB y 6 puertos de entrada/salida de alta velocidad.'
  },
  {
    id: 'motors',
    name: 'Motores Angulares (Grande y Mediano)',
    tag: 'Tracción y Precisión',
    description:
      'Motores con sensores de rotación integrados que permiten controlar velocidad, ángulo exacto y torque para brazos mecánicos, pinzas y tracción.'
  },
  {
    id: 'sensors',
    name: 'Sensores de Color, Distancia y Fuerza',
    tag: 'Percepción Óptica y Táctil',
    description:
      'Sensor ultrasónico de distancia con ojos LED, sensor óptico capaz de distinguir colores e intensidad de luz, y sensor de fuerza/tacto de alta sensibilidad.'
  },
  {
    id: 'technic',
    name: 'Piezas y Vigas LEGO Technic',
    tag: 'Chasis y Engranajes',
    description:
      'Vigas modulares, conectores, engranajes diferenciales, ejes y ruedas de baja fricción diseñadas para construir estructuras resistentes de competencia.'
  }
];

const ARDUINO_PARTS = [
  {
    id: 'board',
    name: 'Placa Microcontroladora Arduino UNO',
    tag: 'Microcontrolador C++',
    description:
      'Placa electrónica programable con pines digitales PWM, entradas analógicas, regulador de voltaje y conexión USB para ejecutar código en tiempo real.'
  },
  {
    id: 'protoboard',
    name: 'Protoboard y Cables Jumper',
    tag: 'Prototipado Sin Soldadura',
    description:
      'Tablero de pruebas que permite interconectar resistencias, circuitos integrados y módulos electrónicos de forma segura, ordenada y modular.'
  },
  {
    id: 'arduino_sensors',
    name: 'Sensor Ultrasónico HC-SR04 y Servomotores',
    tag: 'Distancia y Movimiento Angular',
    description:
      'Sensor ultrasónico HC-SR04 para medición precisa de obstáculos por ecolocalización y servomotores de precisión angular (0° a 180°).'
  },
  {
    id: 'actuators',
    name: 'LEDs, Resistencias y Módulos Electrónicos',
    tag: 'Señalización y Control',
    description:
      'Diodos LED de alto brillo, resistencias de protección, buzzers acústicos y controladores de potencia para prototipos mecatrónicos completos.'
  }
];

const WINDOW_CATALOG = [
  { id: 'inicio', exeName: 'TECH_MASTERS_Inicio.exe', label: 'Inicio Club', sectionId: 'que-es', dotColor: '#0078D7' },
  { id: 'python', exeName: 'Python_AI.exe', label: 'Python', sectionId: 'que-ensenamos', dotColor: '#10B981' },
  { id: 'html', exeName: 'HTML5_Estructura.exe', label: 'HTML5', sectionId: 'que-ensenamos', dotColor: '#F97316' },
  { id: 'javascript', exeName: 'JS_Motor.exe', label: 'JavaScript', sectionId: 'que-ensenamos', dotColor: '#EAB308' },
  { id: 'css', exeName: 'CSS3_Aero.exe', label: 'CSS3 Aero', sectionId: 'que-ensenamos', dotColor: '#0EA5E9' },
  { id: 'spike', exeName: 'LEGO_SpikePrime.exe', label: 'SPIKE PRIME', sectionId: 'que-ensenamos', dotColor: '#8B5CF6' },
  { id: 'arduino', exeName: 'Arduino_Robotica.exe', label: 'Arduino', sectionId: 'que-ensenamos', dotColor: '#F43F5E' },
  { id: 'qr', exeName: 'QR_Movil_Sync.exe', label: 'Código QR', sectionId: 'acceso-qr', dotColor: '#00B4FF' }
];

/**
 * ============================================================================
 * ILUSTRACIÓN VECTORIAL SVG FRUTIGER AERO (NÚCLEO ROBÓTICO - 100% CREATEELEMENT)
 * ============================================================================
 */
const RoboticCoreIllustration = ({ scanMode, onToggleScan }) => {
  return el(
    'div',
    {
      onClick: onToggleScan,
      role: 'button',
      tabIndex: 0,
      onKeyDown: (ev) => {
        if (ev.key === 'Enter' || ev.key === ' ') onToggleScan();
      },
      title: 'Haz clic para alternar el modo de escaneo óptico IA',
      className: 'relative w-full max-w-md mx-auto cursor-pointer select-none group'
    },
    // Halo luminoso Aero
    el('div', {
      className: `absolute inset-4 rounded-full blur-2xl transition-all duration-700 ${
        scanMode
          ? 'bg-gradient-to-tr from-[#0078D7]/45 via-[#00B4FF]/55 to-white/75 scale-105'
          : 'bg-gradient-to-tr from-[#0078D7]/25 via-[#38BDF8]/35 to-white/60'
      }`
    }),
    // SVG Vectorial puro
    el(
      'svg',
      {
        viewBox: '0 0 420 420',
        className:
          'relative z-10 w-full h-auto drop-shadow-[0_20px_35px_rgba(0,120,215,0.24)] transition-transform duration-500 group-hover:scale-[1.03]',
        'aria-label': 'Núcleo Robótico Frutiger Aero TECH MASTERS'
      },
      el(
        'defs',
        null,
        el(
          'linearGradient',
          { id: 'aeroMetal', x1: '0%', y1: '0%', x2: '100%', y2: '100%' },
          el('stop', { offset: '0%', stopColor: '#FFFFFF' }),
          el('stop', { offset: '45%', stopColor: '#E2E8F0' }),
          el('stop', { offset: '80%', stopColor: '#94A3B8' }),
          el('stop', { offset: '100%', stopColor: '#CBD5E1' })
        ),
        el(
          'linearGradient',
          { id: 'aeroWhiteShell', x1: '0%', y1: '0%', x2: '0%', y2: '100%' },
          el('stop', { offset: '0%', stopColor: '#FFFFFF' }),
          el('stop', { offset: '65%', stopColor: '#F1F5F9' }),
          el('stop', { offset: '100%', stopColor: '#CBD5E1' })
        ),
        el(
          'linearGradient',
          { id: 'aeroBlueCore', x1: '0%', y1: '0%', x2: '100%', y2: '100%' },
          el('stop', { offset: '0%', stopColor: '#38BDF8' }),
          el('stop', { offset: '50%', stopColor: '#00B4FF' }),
          el('stop', { offset: '100%', stopColor: '#0078D7' })
        ),
        el(
          'linearGradient',
          { id: 'glossOverlay', x1: '0%', y1: '0%', x2: '0%', y2: '100%' },
          el('stop', { offset: '0%', stopColor: '#FFFFFF', stopOpacity: '0.9' }),
          el('stop', { offset: '50%', stopColor: '#FFFFFF', stopOpacity: '0.25' }),
          el('stop', { offset: '100%', stopColor: '#FFFFFF', stopOpacity: '0.0' })
        ),
        el(
          'radialGradient',
          { id: 'opticGlow', cx: '50%', cy: '50%', r: '50%' },
          el('stop', { offset: '0%', stopColor: '#FFFFFF' }),
          el('stop', { offset: '30%', stopColor: '#7DD3FC' }),
          el('stop', { offset: '70%', stopColor: '#00B4FF' }),
          el('stop', { offset: '100%', stopColor: '#0078D7' })
        )
      ),
      // Anillos orbitales
      el('circle', {
        cx: '210',
        cy: '210',
        r: '185',
        fill: 'none',
        stroke: 'url(#aeroBlueCore)',
        strokeWidth: '1.5',
        strokeDasharray: '10 8',
        opacity: '0.5'
      }),
      el('circle', {
        cx: '210',
        cy: '210',
        r: '158',
        fill: 'none',
        stroke: '#FFFFFF',
        strokeWidth: '2.5',
        opacity: '0.88'
      }),
      // Burbujas Aero flotantes
      el(
        'g',
        { className: 'aero-float-slow' },
        el('circle', { cx: '66', cy: '115', r: '22', fill: 'url(#aeroBlueCore)', opacity: '0.85' }),
        el('ellipse', { cx: '60', cy: '107', rx: '11', ry: '6', fill: '#FFFFFF', opacity: '0.8' })
      ),
      el(
        'g',
        { className: 'aero-float-reverse' },
        el('circle', {
          cx: '356',
          cy: '135',
          r: '16',
          fill: 'url(#aeroMetal)',
          stroke: '#FFFFFF',
          strokeWidth: '2'
        }),
        el('ellipse', { cx: '352', cy: '130', rx: '7', ry: '4', fill: '#FFFFFF', opacity: '0.9' })
      ),
      el(
        'g',
        { className: 'aero-float-slow' },
        el('circle', { cx: '342', cy: '312', r: '25', fill: 'url(#aeroBlueCore)', opacity: '0.78' }),
        el('ellipse', { cx: '335', cy: '303', rx: '12', ry: '7', fill: '#FFFFFF', opacity: '0.75' })
      ),
      // Estabilizadores laterales metálicos
      el('rect', {
        x: '58',
        y: '168',
        width: '36',
        height: '84',
        rx: '18',
        fill: 'url(#aeroMetal)',
        stroke: '#FFFFFF',
        strokeWidth: '2.5'
      }),
      el('rect', { x: '68', y: '184', width: '10', height: '52', rx: '5', fill: '#00B4FF', opacity: '0.9' }),
      el('rect', {
        x: '326',
        y: '168',
        width: '36',
        height: '84',
        rx: '18',
        fill: 'url(#aeroMetal)',
        stroke: '#FFFFFF',
        strokeWidth: '2.5'
      }),
      el('rect', { x: '342', y: '184', width: '10', height: '52', rx: '5', fill: '#00B4FF', opacity: '0.9' }),
      // Antena energética superior
      el('rect', {
        x: '202',
        y: '46',
        width: '16',
        height: '44',
        rx: '8',
        fill: 'url(#aeroMetal)',
        stroke: '#FFFFFF',
        strokeWidth: '2'
      }),
      el('circle', {
        cx: '210',
        cy: '40',
        r: '15',
        fill: 'url(#aeroBlueCore)',
        stroke: '#FFFFFF',
        strokeWidth: '2.5'
      }),
      el('ellipse', { cx: '206', cy: '35', rx: '6', ry: '3.5', fill: '#FFFFFF', opacity: '0.9' }),
      // Casco robótico blanco cristalino
      el('rect', {
        x: '88',
        y: '84',
        width: '244',
        height: '244',
        rx: '76',
        fill: 'url(#aeroWhiteShell)',
        stroke: '#FFFFFF',
        strokeWidth: '4'
      }),
      el('rect', {
        x: '106',
        y: '102',
        width: '208',
        height: '208',
        rx: '62',
        fill: 'none',
        stroke: '#CBD5E1',
        strokeWidth: '3'
      }),
      // Visor cristalino azul oscuro
      el('rect', {
        x: '118',
        y: '134',
        width: '184',
        height: '122',
        rx: '48',
        fill: '#0F172A',
        stroke: 'url(#aeroBlueCore)',
        strokeWidth: '3.5'
      }),
      // Ópticas Cyan brillantes
      el(
        'g',
        null,
        el('circle', {
          cx: '168',
          cy: '195',
          r: scanMode ? '28' : '24',
          fill: 'url(#opticGlow)',
          className: 'transition-all duration-300'
        }),
        el('circle', { cx: '168', cy: '195', r: '11', fill: '#0F172A', opacity: '0.35' }),
        el('circle', { cx: '160', cy: '186', r: '6', fill: '#FFFFFF', opacity: '0.95' }),
        el('circle', {
          cx: '252',
          cy: '195',
          r: scanMode ? '28' : '24',
          fill: 'url(#opticGlow)',
          className: 'transition-all duration-300'
        }),
        el('circle', { cx: '252', cy: '195', r: '11', fill: '#0F172A', opacity: '0.35' }),
        el('circle', { cx: '244', cy: '186', r: '6', fill: '#FFFFFF', opacity: '0.95' })
      ),
      // Línea de telemetría / sonrisa digital
      el('path', {
        d: scanMode ? 'M 178 232 Q 210 246 242 232' : 'M 184 232 L 236 232',
        stroke: '#38BDF8',
        strokeWidth: '4',
        strokeLinecap: 'round',
        fill: 'none'
      }),
      // Reflejo Glossy superior sobre el visor
      el('path', {
        d: 'M 134 146 C 165 136, 255 136, 286 146 C 292 162, 284 174, 268 174 C 235 168, 185 168, 152 174 C 136 174, 128 162, 134 146 Z',
        fill: 'url(#glossOverlay)'
      }),
      // Módulo pectoral inferior
      el('rect', {
        x: '156',
        y: '272',
        width: '108',
        height: '32',
        rx: '16',
        fill: 'url(#aeroMetal)',
        stroke: '#FFFFFF',
        strokeWidth: '2'
      }),
      el('circle', { cx: '182', cy: '288', r: '6', fill: '#00B4FF' }),
      el('circle', { cx: '210', cy: '288', r: '7', fill: '#0078D7' }),
      el('circle', { cx: '238', cy: '288', r: '6', fill: '#38BDF8' })
    ),
    // Etiqueta interactiva inferior
    el(
      'div',
      { className: 'mt-2 flex justify-center' },
      el(
        'span',
        {
          className:
            'inline-flex items-center gap-2 px-4 py-1.5 rounded-full text-xs font-bold text-[#0052A3] bg-white/85 backdrop-blur-md border border-white shadow-sm'
        },
        el(Eye, { className: 'w-3.5 h-3.5 text-[#00B4FF]' }),
        scanMode
          ? 'Modo Escaneo IA Activo (Clic para cambiar)'
          : 'Núcleo Robótico v3.0 (Clic para activar Escaneo IA)'
      )
    )
  );
};

/**
 * ============================================================================
 * DIAGRAMAS SVG INTERACTIVOS PARA LEGO SPIKE PRIME Y ARDUINO (100% CREATEELEMENT)
 * ============================================================================
 */
const SpikePrimeDiagram = ({ activePartId, onSelectPart }) => {
  const isSelected = (id) => activePartId === id;

  const ledCells = [];
  for (let row = 0; row < 5; row++) {
    for (let col = 0; col < 5; col++) {
      const lit =
        (row === 1 && (col === 1 || col === 3)) ||
        (row === 3 && col >= 1 && col <= 3) ||
        (row === 2 && col === 2);
      ledCells.push(
        el('rect', {
          key: `${row}-${col}`,
          x: 236 + col * 15,
          y: 77 + row * 14,
          width: '9',
          height: '9',
          rx: '2',
          fill: lit ? '#00B4FF' : '#CBD5E1'
        })
      );
    }
  }

  return el(
    'div',
    {
      className:
        'relative w-full bg-gradient-to-b from-white/90 to-[#E0F2FE]/85 rounded-2xl p-3.5 border border-white shadow-inner'
    },
    el(
      'svg',
      {
        viewBox: '0 0 540 270',
        className: 'w-full h-auto',
        'aria-label': 'Diagrama interactivo del kit LEGO SPIKE PRIME'
      },
      el(
        'defs',
        null,
        el(
          'linearGradient',
          { id: 'spikeHubGrad', x1: '0%', y1: '0%', x2: '0%', y2: '100%' },
          el('stop', { offset: '0%', stopColor: '#FFFFFF' }),
          el('stop', { offset: '100%', stopColor: '#E2E8F0' })
        ),
        el(
          'linearGradient',
          { id: 'spikeBlueAccent', x1: '0%', y1: '0%', x2: '100%', y2: '100%' },
          el('stop', { offset: '0%', stopColor: '#38BDF8' }),
          el('stop', { offset: '100%', stopColor: '#0078D7' })
        )
      ),
      // Cables
      el('path', { d: 'M 195 135 C 150 135, 145 78, 118 78', stroke: '#64748B', strokeWidth: '4', fill: 'none' }),
      el('path', { d: 'M 195 155 C 150 155, 145 198, 118 198', stroke: '#00B4FF', strokeWidth: '4', fill: 'none' }),
      el('path', { d: 'M 345 135 C 390 135, 395 78, 422 78', stroke: '#0078D7', strokeWidth: '4', fill: 'none' }),
      el('path', { d: 'M 345 155 C 390 155, 395 198, 422 198', stroke: '#94A3B8', strokeWidth: '4', fill: 'none' }),
      // 1. HUB INTELIGENTE
      el(
        'g',
        {
          onClick: () => onSelectPart('hub'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.03]'
        },
        el('rect', {
          x: '195',
          y: '45',
          width: '150',
          height: '180',
          rx: '22',
          fill: 'url(#spikeHubGrad)',
          stroke: isSelected('hub') ? '#00B4FF' : '#94A3B8',
          strokeWidth: isSelected('hub') ? '4' : '2'
        }),
        el('path', {
          d: 'M 195 195 L 345 195 L 345 205 Q 345 225 325 225 L 215 225 Q 195 225 195 205 Z',
          fill: 'url(#spikeBlueAccent)'
        }),
        el('rect', {
          x: '225',
          y: '68',
          width: '90',
          height: '82',
          rx: '10',
          fill: '#F8FAFC',
          stroke: '#CBD5E1',
          strokeWidth: '1.5'
        }),
        ...ledCells,
        el('circle', { cx: '270', cy: '172', r: '13', fill: '#FFFFFF', stroke: '#0078D7', strokeWidth: '2.5' }),
        el(
          'text',
          { x: '270', y: '246', textAnchor: 'middle', fontSize: '11', fontWeight: '800', fill: '#0F172A' },
          'Hub Inteligente 5x5'
        )
      ),
      // 2. MOTORES ANGULARES
      el(
        'g',
        {
          onClick: () => onSelectPart('motors'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.04]'
        },
        el('rect', {
          x: '24',
          y: '34',
          width: '98',
          height: '86',
          rx: '16',
          fill: '#FFFFFF',
          stroke: isSelected('motors') ? '#00B4FF' : '#CBD5E1',
          strokeWidth: isSelected('motors') ? '3.5' : '2'
        }),
        el('circle', { cx: '73', cy: '74', r: '24', fill: 'url(#spikeBlueAccent)' }),
        el('circle', { cx: '73', cy: '74', r: '12', fill: '#FFFFFF' }),
        el('path', { d: 'M 73 54 L 73 94 M 53 74 L 93 74', stroke: '#0078D7', strokeWidth: '2.5' }),
        el(
          'text',
          { x: '73', y: '135', textAnchor: 'middle', fontSize: '10.5', fontWeight: '800', fill: '#1E293B' },
          'Motores Angulares'
        )
      ),
      // 3. SENSORES
      el(
        'g',
        {
          onClick: () => onSelectPart('sensors'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.04]'
        },
        el('rect', {
          x: '418',
          y: '34',
          width: '98',
          height: '86',
          rx: '16',
          fill: '#FFFFFF',
          stroke: isSelected('sensors') ? '#00B4FF' : '#CBD5E1',
          strokeWidth: isSelected('sensors') ? '3.5' : '2'
        }),
        el('circle', { cx: '448', cy: '75', r: '16', fill: '#0F172A', stroke: '#00B4FF', strokeWidth: '3' }),
        el('circle', { cx: '486', cy: '75', r: '16', fill: '#0F172A', stroke: '#00B4FF', strokeWidth: '3' }),
        el('circle', { cx: '448', cy: '75', r: '6', fill: '#38BDF8' }),
        el('circle', { cx: '486', cy: '75', r: '6', fill: '#38BDF8' }),
        el(
          'text',
          { x: '467', y: '135', textAnchor: 'middle', fontSize: '10.5', fontWeight: '800', fill: '#1E293B' },
          'Sensores Ópticos'
        )
      ),
      // 4. PIEZAS TECHNIC
      el(
        'g',
        {
          onClick: () => onSelectPart('technic'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.04]'
        },
        el('rect', {
          x: '24',
          y: '156',
          width: '98',
          height: '82',
          rx: '16',
          fill: '#FFFFFF',
          stroke: isSelected('technic') ? '#00B4FF' : '#CBD5E1',
          strokeWidth: isSelected('technic') ? '3.5' : '2'
        }),
        el('rect', { x: '38', y: '186', width: '70', height: '16', rx: '8', fill: '#0078D7' }),
        ...[48, 60, 72, 84, 96].map((cx) =>
          el('circle', { key: cx, cx: String(cx), cy: '194', r: '3.5', fill: '#FFFFFF' })
        ),
        el(
          'text',
          { x: '73', y: '254', textAnchor: 'middle', fontSize: '10.5', fontWeight: '800', fill: '#1E293B' },
          'Vigas Technic'
        )
      ),
      el(
        'g',
        {
          onClick: () => onSelectPart('technic'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.04]'
        },
        el('rect', {
          x: '418',
          y: '156',
          width: '98',
          height: '82',
          rx: '16',
          fill: '#FFFFFF',
          stroke: isSelected('technic') ? '#00B4FF' : '#CBD5E1',
          strokeWidth: isSelected('technic') ? '3.5' : '2'
        }),
        el('circle', {
          cx: '467',
          cy: '196',
          r: '22',
          fill: 'none',
          stroke: '#64748B',
          strokeWidth: '6',
          strokeDasharray: '7 4'
        }),
        el('circle', { cx: '467', cy: '196', r: '9', fill: '#00B4FF' }),
        el(
          'text',
          { x: '467', y: '254', textAnchor: 'middle', fontSize: '10.5', fontWeight: '800', fill: '#1E293B' },
          'Engranajes y Ruedas'
        )
      )
    )
  );
};

const ArduinoDiagram = ({ activePartId, onSelectPart }) => {
  const isSelected = (id) => activePartId === id;

  const protoPins = [];
  for (let idx = 0; idx < 8; idx++) {
    protoPins.push(
      el('circle', { key: `t-${idx}`, cx: String(332 + idx * 22), cy: '66', r: '2.5', fill: '#94A3B8' }),
      el('circle', { key: `b-${idx}`, cx: String(332 + idx * 22), cy: '100', r: '2.5', fill: '#94A3B8' })
    );
  }

  return el(
    'div',
    {
      className:
        'relative w-full bg-gradient-to-b from-white/90 to-[#E0F2FE]/85 rounded-2xl p-3.5 border border-white shadow-inner'
    },
    el(
      'svg',
      {
        viewBox: '0 0 540 270',
        className: 'w-full h-auto',
        'aria-label': 'Diagrama interactivo de Robótica Avanzada con Arduino'
      },
      el(
        'defs',
        null,
        el(
          'linearGradient',
          { id: 'arduinoPcb', x1: '0%', y1: '0%', x2: '100%', y2: '100%' },
          el('stop', { offset: '0%', stopColor: '#00B4FF' }),
          el('stop', { offset: '100%', stopColor: '#0078D7' })
        )
      ),
      // Cables Jumper
      el('path', { d: 'M 190 95 C 235 60, 275 60, 315 88', stroke: '#00B4FF', strokeWidth: '3.5', fill: 'none' }),
      el('path', { d: 'M 190 112 C 235 80, 275 80, 315 106', stroke: '#38BDF8', strokeWidth: '3.5', fill: 'none' }),
      el('path', { d: 'M 190 165 C 235 195, 275 195, 315 175', stroke: '#64748B', strokeWidth: '3.5', fill: 'none' }),
      // 1. PLACA ARDUINO UNO
      el(
        'g',
        {
          onClick: () => onSelectPart('board'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.03]'
        },
        el('rect', {
          x: '26',
          y: '55',
          width: '172',
          height: '145',
          rx: '14',
          fill: 'url(#arduinoPcb)',
          stroke: isSelected('board') ? '#38BDF8' : '#FFFFFF',
          strokeWidth: isSelected('board') ? '4' : '2.5'
        }),
        el('rect', { x: '14', y: '75', width: '32', height: '34', rx: '4', fill: '#CBD5E1', stroke: '#64748B', strokeWidth: '1.5' }),
        el('rect', { x: '16', y: '145', width: '28', height: '26', rx: '4', fill: '#1E293B' }),
        el('rect', { x: '74', y: '138', width: '84', height: '24', rx: '3', fill: '#0F172A', stroke: '#94A3B8', strokeWidth: '1' }),
        el('rect', { x: '64', y: '65', width: '114', height: '12', rx: '2', fill: '#0F172A' }),
        el(
          'text',
          { x: '112', y: '114', textAnchor: 'middle', fontSize: '13', fontWeight: '900', fill: '#FFFFFF' },
          'ARDUINO UNO'
        ),
        el(
          'text',
          { x: '112', y: '220', textAnchor: 'middle', fontSize: '11', fontWeight: '800', fill: '#0F172A' },
          'Placa Microcontroladora'
        )
      ),
      // 2. PROTOBOARD Y CABLES JUMPER
      el(
        'g',
        {
          onClick: () => onSelectPart('protoboard'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.03]'
        },
        el('rect', {
          x: '306',
          y: '38',
          width: '206',
          height: '92',
          rx: '12',
          fill: '#FFFFFF',
          stroke: isSelected('protoboard') ? '#00B4FF' : '#CBD5E1',
          strokeWidth: isSelected('protoboard') ? '3.5' : '2'
        }),
        el('line', { x1: '318', y1: '52', x2: '500', y2: '52', stroke: '#00B4FF', strokeWidth: '2' }),
        el('line', { x1: '318', y1: '116', x2: '500', y2: '116', stroke: '#64748B', strokeWidth: '2' }),
        el('rect', { x: '318', y: '80', width: '182', height: '8', rx: '2', fill: '#E2E8F0' }),
        ...protoPins,
        el(
          'text',
          { x: '409', y: '146', textAnchor: 'middle', fontSize: '10.5', fontWeight: '800', fill: '#1E293B' },
          'Protoboard y Circuitos'
        )
      ),
      // 3. SENSOR HC-SR04 Y SERVOS
      el(
        'g',
        {
          onClick: () => onSelectPart('arduino_sensors'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.04]'
        },
        el('rect', {
          x: '286',
          y: '162',
          width: '106',
          height: '72',
          rx: '12',
          fill: '#0078D7',
          stroke: isSelected('arduino_sensors') ? '#38BDF8' : '#FFFFFF',
          strokeWidth: isSelected('arduino_sensors') ? '3.5' : '2'
        }),
        el('circle', { cx: '316', cy: '198', r: '17', fill: '#E2E8F0', stroke: '#94A3B8', strokeWidth: '2.5' }),
        el('circle', { cx: '362', cy: '198', r: '17', fill: '#E2E8F0', stroke: '#94A3B8', strokeWidth: '2.5' }),
        el(
          'text',
          { x: '339', y: '250', textAnchor: 'middle', fontSize: '10.5', fontWeight: '800', fill: '#1E293B' },
          'HC-SR04 y Servos'
        )
      ),
      // 4. LEDS Y RESISTENCIAS
      el(
        'g',
        {
          onClick: () => onSelectPart('actuators'),
          className: 'cursor-pointer transition-transform duration-300 hover:scale-[1.04]'
        },
        el('rect', {
          x: '408',
          y: '162',
          width: '106',
          height: '72',
          rx: '12',
          fill: '#FFFFFF',
          stroke: isSelected('actuators') ? '#00B4FF' : '#CBD5E1',
          strokeWidth: isSelected('actuators') ? '3.5' : '2'
        }),
        el('rect', { x: '424', y: '178', width: '42', height: '38', rx: '6', fill: '#0F172A' }),
        el('circle', { cx: '445', cy: '197', r: '10', fill: '#00B4FF' }),
        el('rect', { x: '474', y: '182', width: '26', height: '30', rx: '4', fill: '#E0F2FE', stroke: '#00B4FF', strokeWidth: '1.5' }),
        el(
          'text',
          { x: '461', y: '250', textAnchor: 'middle', fontSize: '10.5', fontWeight: '800', fill: '#1E293B' },
          'LEDs y Módulos'
        )
      )
    )
  );
};

/**
 * ============================================================================
 * COMPONENTE DE VENTANA POP-UP DE WINDOWS VISTA / 7 AERO GLASS
 * ============================================================================
 */
const AeroWindow = ({
  id,
  exeName,
  subtitle,
  icon: IconComp,
  statusText,
  theme,
  isMinimized,
  isClosed,
  onMinimize,
  onMaximize,
  onClose,
  className = '',
  children
}) => {
  if (isClosed) return null;

  const windowVars = theme
    ? {
        background: theme.windowBg,
        '--win-ring': theme.ringColor,
        '--win-hover-ring': theme.hoverRingColor,
        '--win-shadow': theme.shadowColor,
        '--win-hover-shadow': theme.hoverShadowColor
      }
    : undefined;

  return el(
    'div',
    {
      id: `win-popup-${id}`,
      style: windowVars,
      className: `win-aero-window rounded-2xl overflow-hidden flex flex-col ${className}`
    },
    // BARRA DE TÍTULO TRANSLÚCIDA WINDOWS VISTA / 7 AERO (SPLIT GLOSS 50/50)
    el(
      'div',
      {
        onDoubleClick: onMaximize,
        style: theme ? { background: theme.titlebarGradient } : undefined,
        className:
          'win-aero-titlebar px-3.5 py-2.5 flex items-center justify-between gap-2 select-none border-b border-white/80'
      },
      // Izquierda: Icono de programa + Nombre de ejecutable .exe
      el(
        'div',
        { className: 'flex items-center gap-2.5 min-w-0' },
        el(
          'div',
          {
            style: theme ? { background: theme.iconGradient } : undefined,
            className:
              'w-7 h-7 rounded-lg bg-gradient-to-b from-[#38BDF8] via-[#00B4FF] to-[#0078D7] text-white flex items-center justify-center border border-white/90 shadow-sm shrink-0'
          },
          el(IconComp, { className: 'w-4 h-4' })
        ),
        el(
          'div',
          { className: 'flex items-center gap-2 min-w-0' },
          el(
            'span',
            {
              className:
                'win-aero-title-label text-xs sm:text-sm font-extrabold tracking-tight text-[#0F172A] truncate'
            },
            exeName
          ),
          subtitle
            ? el(
                'span',
                {
                  style: theme
                    ? { backgroundColor: theme.badgeBg, color: theme.badgeText }
                    : undefined,
                  className:
                    'hidden sm:inline-block px-2 py-0.5 rounded-md text-[10px] font-bold bg-white/75 text-[#0052A3] border border-white truncate'
                },
                subtitle
              )
            : null
        )
      ),
      // Derecha: Botones reales de control de Windows (Minimizar, Maximizar, Cerrar)
      el(
        'div',
        { className: 'flex items-center gap-1 shrink-0' },
        // Minimizar (—)
        el(
          'button',
          {
            type: 'button',
            onClick: (ev) => {
              ev.stopPropagation();
              onMinimize();
            },
            title: isMinimized ? 'Expandir ventana' : 'Minimizar ventana',
            'aria-label': 'Minimizar',
            className:
              'win-caption-btn win-caption-min w-7 h-6 rounded-md flex items-center justify-center text-[#0F172A] font-black text-xs cursor-pointer'
          },
          '—'
        ),
        // Maximizar (□)
        el(
          'button',
          {
            type: 'button',
            onClick: (ev) => {
              ev.stopPropagation();
              onMaximize();
            },
            title: 'Maximizar en ventana emergente Aero',
            'aria-label': 'Maximizar',
            className:
              'win-caption-btn win-caption-max w-7 h-6 rounded-md flex items-center justify-center text-[#0F172A] font-black text-xs cursor-pointer'
          },
          '□'
        ),
        // Cerrar (✕) en rojo brillante Windows Aero
        el(
          'button',
          {
            type: 'button',
            onClick: (ev) => {
              ev.stopPropagation();
              onClose();
            },
            title: 'Cerrar ventana (minimizar a la barra de tareas)',
            'aria-label': 'Cerrar',
            className:
              'win-caption-btn win-caption-close w-8 h-6 rounded-md flex items-center justify-center text-white font-black text-xs cursor-pointer'
          },
          '✕'
        )
      )
    ),
    // CUERPO INTERIOR DE LA VENTANA (Colapsable al minimizar)
    !isMinimized
      ? el(
          'div',
          { className: 'win-aero-body flex-1 p-5 sm:p-6 lg:p-7 flex flex-col justify-between' },
          children
        )
      : null,
    // BARRA DE ESTADO INFERIOR CON METADATOS TÉCNICOS
    el(
      'div',
      {
        style: theme
          ? {
              background: theme.statusbarBg,
              borderTopColor: theme.statusbarBorder
            }
          : undefined,
        className:
          'win-aero-statusbar px-3.5 py-1.5 flex items-center justify-between gap-2 text-[11px] font-semibold text-[#334155]'
      },
      el(
        'div',
        { className: 'flex items-center gap-2 truncate' },
        el('span', {
          style:
            !isMinimized && theme
              ? {
                  backgroundColor: theme.ledColor,
                  boxShadow: `0 0 7px ${theme.ledColor}`
                }
              : undefined,
          className: `w-2 h-2 rounded-full shrink-0 ${
            isMinimized ? 'bg-amber-400' : 'bg-[#06B6D4] shadow-[0_0_6px_#06B6D4]'
          }`
        }),
        el('span', { className: 'truncate' }, isMinimized ? `${exeName} (Minimizada)` : statusText)
      ),
      el(
        'span',
        { className: 'text-[10px] font-mono text-[#64748B] select-none shrink-0' },
        '◢'
      )
    )
  );
};

/**
 * ============================================================================
 * APLICACIÓN PRINCIPAL TECH MASTERS (100% REACT.CREATEELEMENT / ZERO-HTML)
 * ============================================================================
 */
export default function App() {
  const [scanMode, setScanMode] = useState(false);
  const [minimizedMap, setMinimizedMap] = useState({});
  const [closedMap, setClosedMap] = useState({});
  const [maximizedWindowId, setMaximizedWindowId] = useState(null);
  const [startMenuOpen, setStartMenuOpen] = useState(false);
  const [copiedCode, setCopiedCode] = useState(false);
  const [clockText, setClockText] = useState('');

  // Estado interactivo de la división de robótica
  const [spikeTab, setSpikeTab] = useState('parts');
  const [activeSpikePart, setActiveSpikePart] = useState('hub');

  const [arduinoTab, setArduinoTab] = useState('parts');
  const [activeArduinoPart, setActiveArduinoPart] = useState('board');

  // Estado del generador QR en tiempo real
  const defaultUrl = useMemo(() => {
    try {
      if (typeof window !== 'undefined' && window.location && window.location.href) {
        return window.location.href;
      }
    } catch (_) {
      // Fallback seguro
    }
    return 'https://techmasters-club.edu';
  }, []);

  const [qrUrl, setQrUrl] = useState(defaultUrl);
  const qrCanvasRef = useRef(null);

  // Reloj en vivo para la bandeja del sistema de Windows Aero
  useEffect(() => {
    const updateClock = () => {
      const now = new Date();
      const hh = String(now.getHours()).padStart(2, '0');
      const mm = String(now.getMinutes()).padStart(2, '0');
      setClockText(`${hh}:${mm}`);
    };
    updateClock();
    const timer = setInterval(updateClock, 15000);
    return () => clearInterval(timer);
  }, []);

  // Inyección dinámica de fuentes Frutiger Aero y estilos Windows Aero Glass desde JS puro
  useEffect(() => {
    const fontLinkId = 'tech-masters-aero-fonts';
    if (!document.getElementById(fontLinkId)) {
      const linkEl = document.createElement('link');
      linkEl.id = fontLinkId;
      linkEl.rel = 'stylesheet';
      linkEl.href =
        'https://fonts.googleapis.com/css2?family=Exo+2:ital,wght@0,600;0,700;0,800;0,900;1,700&family=Nunito+Sans:wght@400;600;700;800&family=Plus+Jakarta+Sans:wght@500;700;800&display=swap';
      document.head.appendChild(linkEl);
    }

    const styleId = 'tech-masters-frutiger-aero-css';
    if (!document.getElementById(styleId)) {
      const styleEl = document.createElement('style');
      styleEl.id = styleId;
      styleEl.textContent = `
        html {
          scroll-behavior: smooth;
          font-family: 'Nunito Sans', 'Segoe UI', 'Frutiger', sans-serif;
        }
        h1, h2, h3, h4, .aero-font-display {
          font-family: 'Exo 2', 'Plus Jakarta Sans', 'Segoe UI', 'Frutiger', sans-serif;
        }
        @keyframes aeroFloatSlow {
          0%, 100% { transform: translateY(0px) translateX(0px); }
          50% { transform: translateY(-14px) translateX(6px); }
        }
        @keyframes aeroFloatReverse {
          0%, 100% { transform: translateY(0px) translateX(0px); }
          50% { transform: translateY(12px) translateX(-8px); }
        }
        .aero-float-slow {
          animation: aeroFloatSlow 6s ease-in-out infinite;
        }
        .aero-float-reverse {
          animation: aeroFloatReverse 7.5s ease-in-out infinite;
        }

        /* LETRAS FRUTIGER AERO GLOSSY CON REFLEJO CRISTALINO Y RESPLANDOR CIAN */
        .frutiger-aero-wordmark {
          position: relative;
          display: inline-block;
          font-family: 'Exo 2', 'Segoe UI', 'Frutiger', sans-serif;
          font-weight: 900;
          letter-spacing: -0.02em;
          background: linear-gradient(
            180deg,
            #FFFFFF 0%,
            #E0F2FE 36%,
            #38BDF8 50%,
            #0078D7 78%,
            #004E92 100%
          );
          -webkit-background-clip: text;
          background-clip: text;
          color: transparent;
          filter: drop-shadow(0 2px 0 rgba(15, 23, 42, 0.72))
                  drop-shadow(0 0 14px rgba(0, 180, 255, 0.65));
        }

        .frutiger-aero-heading {
          font-family: 'Exo 2', 'Segoe UI', 'Frutiger', sans-serif;
          font-weight: 900;
          background: linear-gradient(
            180deg,
            #0F172A 0%,
            #0052A3 46%,
            #0078D7 52%,
            #00B4FF 100%
          );
          -webkit-background-clip: text;
          background-clip: text;
          color: transparent;
          filter: drop-shadow(0 1px 0 rgba(255, 255, 255, 0.95))
                  drop-shadow(0 3px 10px rgba(0, 180, 255, 0.25));
        }

        /* VENTANAS POP-UP ESTILO WINDOWS VISTA / 7 AERO GLASS */
        .win-aero-window {
          position: relative;
          background: rgba(255, 255, 255, 0.82);
          backdrop-filter: blur(16px) saturate(180%);
          -webkit-backdrop-filter: blur(16px) saturate(180%);
          border: 1px solid rgba(255, 255, 255, 0.96);
          box-shadow:
            0 0 0 1px var(--win-ring, rgba(0, 120, 215, 0.32)),
            0 18px 42px var(--win-shadow, rgba(0, 65, 130, 0.2)),
            inset 0 1px 0 rgba(255, 255, 255, 1);
          transition: transform 0.35s cubic-bezier(0.22, 1, 0.36, 1),
                      box-shadow 0.35s ease;
        }
        .win-aero-window::before {
          content: '';
          position: absolute;
          top: 0;
          left: -130%;
          width: 75%;
          height: 100%;
          background: linear-gradient(
            115deg,
            transparent 20%,
            rgba(255, 255, 255, 0.76) 50%,
            transparent 80%
          );
          transform: skewX(-20deg);
          transition: left 0.8s cubic-bezier(0.22, 1, 0.36, 1);
          pointer-events: none;
          z-index: 5;
        }
        .win-aero-window:hover {
          transform: translateY(-4px);
          box-shadow:
            0 0 0 1.5px var(--win-hover-ring, rgba(0, 180, 255, 0.65)),
            0 24px 52px var(--win-hover-shadow, rgba(0, 120, 215, 0.28)),
            inset 0 1px 0 rgba(255, 255, 255, 1);
        }
        .win-aero-window:hover::before {
          left: 150%;
        }

        /* BARRA DE TÍTULO WINDOWS AERO CON REFLEJO DIVIDIDO AL 50% */
        .win-aero-titlebar {
          background: linear-gradient(
            180deg,
            rgba(255, 255, 255, 0.92) 0%,
            rgba(224, 242, 254, 0.76) 49%,
            rgba(0, 120, 215, 0.26) 50%,
            rgba(56, 189, 248, 0.22) 100%
          );
          box-shadow: inset 0 1px 0 rgba(255, 255, 255, 1);
        }
        .win-aero-title-label {
          font-family: 'Exo 2', 'Segoe UI', sans-serif;
          text-shadow: 0 0 10px rgba(255, 255, 255, 0.95), 0 1px 0 rgba(255, 255, 255, 0.9);
        }

        /* BOTONES DE CONTROL DE VENTANA DE WINDOWS AERO */
        .win-caption-btn {
          border: 1px solid rgba(100, 116, 139, 0.45);
          box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.9);
          transition: all 0.2s ease;
        }
        .win-caption-min, .win-caption-max {
          background: linear-gradient(
            180deg,
            rgba(255, 255, 255, 0.9) 0%,
            rgba(226, 232, 240, 0.7) 49%,
            rgba(148, 163, 184, 0.35) 50%,
            rgba(203, 213, 225, 0.65) 100%
          );
        }
        .win-caption-min:hover, .win-caption-max:hover {
          background: linear-gradient(
            180deg,
            #E0F2FE 0%,
            #7DD3FC 49%,
            #00B4FF 50%,
            #0078D7 100%
          );
          color: #FFFFFF;
          border-color: #0078D7;
          box-shadow: 0 0 10px rgba(0, 180, 255, 0.65), inset 0 1px 0 rgba(255, 255, 255, 0.9);
        }
        .win-caption-close {
          background: linear-gradient(
            180deg,
            #FDA4AF 0%,
            #F43F5E 49%,
            #BE123C 50%,
            #E11D48 100%
          );
          border-color: rgba(159, 18, 57, 0.7);
        }
        .win-caption-close:hover {
          background: linear-gradient(
            180deg,
            #FECDD3 0%,
            #FB7185 49%,
            #E11D48 50%,
            #FF1E42 100%
          );
          box-shadow: 0 0 12px rgba(244, 63, 94, 0.8), inset 0 1px 0 rgba(255, 255, 255, 0.95);
        }

        /* BARRA DE ESTADO INFERIOR METÁLICA */
        .win-aero-statusbar {
          background: linear-gradient(180deg, #E2E8F0 0%, #CBD5E1 100%);
          border-top: 1px solid #94A3B8;
          box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.85);
        }

        /* BOTÓN AQUA / AERO LÍQUIDO */
        .aero-btn-primary {
          position: relative;
          overflow: hidden;
          background: linear-gradient(180deg, #38BDF8 0%, #00B4FF 48%, #0078D7 100%);
          border: 1px solid rgba(255, 255, 255, 0.9);
          box-shadow: 0 8px 20px rgba(0, 120, 215, 0.3), inset 0 1px 0 rgba(255, 255, 255, 0.8);
          transition: transform 0.25s ease, box-shadow 0.25s ease, filter 0.25s ease;
        }
        .aero-btn-primary::after {
          content: '';
          position: absolute;
          top: 1px;
          left: 4%;
          right: 4%;
          height: 46%;
          border-radius: 9999px;
          background: linear-gradient(180deg, rgba(255, 255, 255, 0.68) 0%, rgba(255, 255, 255, 0.08) 100%);
          pointer-events: none;
        }
        .aero-btn-primary:hover {
          transform: translateY(-2px);
          filter: brightness(1.06);
          box-shadow: 0 12px 26px rgba(0, 180, 255, 0.42), inset 0 1px 0 rgba(255, 255, 255, 0.95);
        }

        .aero-metal-surface {
          background: linear-gradient(145deg, #FFFFFF 0%, #F1F5F9 48%, #E2E8F0 100%);
          border: 1px solid #CBD5E1;
          box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.95), 0 6px 18px rgba(15, 23, 42, 0.06);
        }

        /* BARRA DE TAREAS FLOTANTE ESTILO WINDOWS 7 AERO */
        .win-aero-taskbar {
          background: linear-gradient(
            180deg,
            rgba(224, 242, 254, 0.86) 0%,
            rgba(56, 189, 248, 0.42) 49%,
            rgba(15, 23, 42, 0.82) 50%,
            rgba(30, 41, 59, 0.92) 100%
          );
          backdrop-filter: blur(20px) saturate(190%);
          -webkit-backdrop-filter: blur(20px) saturate(190%);
          border: 1px solid rgba(255, 255, 255, 0.78);
          box-shadow: 0 12px 35px rgba(0, 45, 95, 0.35), inset 0 1px 0 rgba(255, 255, 255, 0.9);
        }

        /* ORBE DE INICIO DE WINDOWS AERO */
        .win-start-orb {
          background: radial-gradient(
            circle at 50% 30%,
            #BAE6FD 0%,
            #00B4FF 38%,
            #0078D7 72%,
            #003B73 100%
          );
          border: 2px solid rgba(255, 255, 255, 0.92);
          box-shadow:
            0 0 18px rgba(0, 180, 255, 0.75),
            inset 0 2px 4px rgba(255, 255, 255, 0.95);
          transition: transform 0.25s ease, box-shadow 0.25s ease;
        }
        .win-start-orb:hover {
          transform: scale(1.08);
          box-shadow:
            0 0 25px rgba(56, 189, 248, 0.95),
            inset 0 2px 6px rgba(255, 255, 255, 1);
        }
      `;
      document.head.appendChild(styleEl);
    }
  }, []);

  // Renderizado del código QR real en Canvas cada vez que cambia qrUrl
  useEffect(() => {
    const canvas = qrCanvasRef.current;
    if (!canvas) return;

    try {
      const targetText = qrUrl.trim() || defaultUrl;
      const { matrix, size } = QR_ENGINE.generateMatrix(targetText);
      const quietZone = 4;
      const totalModules = size + quietZone * 2;
      const scale = 8;
      const pixelSize = totalModules * scale;

      canvas.width = pixelSize;
      canvas.height = pixelSize;

      const ctx = canvas.getContext('2d');
      ctx.fillStyle = '#FFFFFF';
      ctx.fillRect(0, 0, pixelSize, pixelSize);

      for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
          if (matrix[r][c] === 1) {
            ctx.fillStyle = '#0F172A';
            ctx.fillRect(
              (c + quietZone) * scale,
              (r + quietZone) * scale,
              scale,
              scale
            );
          }
        }
      }
    } catch (err) {
      console.error('Error generando matriz QR:', err);
    }
  }, [qrUrl, defaultUrl, closedMap.qr, minimizedMap.qr]);

  const toggleMinimize = (winId) => {
    setMinimizedMap((prev) => ({ ...prev, [winId]: !prev[winId] }));
  };

  const closeWindow = (winId) => {
    setClosedMap((prev) => ({ ...prev, [winId]: true }));
    if (maximizedWindowId === winId) setMaximizedWindowId(null);
  };

  const restoreAndFocusWindow = (winId, sectionId) => {
    setClosedMap((prev) => ({ ...prev, [winId]: false }));
    setMinimizedMap((prev) => ({ ...prev, [winId]: false }));
    setStartMenuOpen(false);
    setTimeout(() => {
      const targetEl =
        document.getElementById(`win-popup-${winId}`) ||
        (sectionId ? document.getElementById(sectionId) : null);
      if (targetEl) {
        targetEl.scrollIntoView({ behavior: 'smooth', block: 'center' });
      }
    }, 60);
  };

  const restoreAllWindows = () => {
    setClosedMap({});
    setMinimizedMap({});
    setStartMenuOpen(false);
  };

  const handleCopyCode = (code) => {
    if (navigator.clipboard) {
      navigator.clipboard.writeText(code).catch(() => {});
    }
    setCopiedCode(true);
    setTimeout(() => setCopiedCode(false), 2000);
  };

  const handleDownloadQR = () => {
    const canvas = qrCanvasRef.current;
    if (!canvas) return;
    const link = document.createElement('a');
    link.download = 'TECH-MASTERS-QR.png';
    link.href = canvas.toDataURL('image/png');
    link.click();
  };

  const currentSpikePart =
    SPIKE_PARTS.find((p) => p.id === activeSpikePart) || SPIKE_PARTS[0];
  const currentArduinoPart =
    ARDUINO_PARTS.find((p) => p.id === activeArduinoPart) || ARDUINO_PARTS[0];

  const anyWindowHidden =
    Object.values(closedMap).some(Boolean) || Object.values(minimizedMap).some(Boolean);

  // Renderizado del contenido del Pop-Up Maximizado de Windows Aero
  const renderMaximizedModal = () => {
    if (!maximizedWindowId) return null;

    const langTopic = PROGRAMMING_TOPICS.find((t) => t.id === maximizedWindowId);
    const catalogItem =
      WINDOW_CATALOG.find((w) => w.id === maximizedWindowId) || WINDOW_CATALOG[0];

    const modalTheme = langTopic
      ? langTopic.theme
      : maximizedWindowId === 'spike'
      ? SPIKE_THEME
      : maximizedWindowId === 'arduino'
      ? ARDUINO_THEME
      : null;

    let modalContent = null;
    if (langTopic) {
      modalContent = el(
        'div',
        { className: 'space-y-5' },
        el(
          'div',
          { className: 'flex items-center gap-3.5' },
          el(
            'div',
            {
              className: 'w-14 h-14 rounded-2xl flex items-center justify-center text-white shadow-lg border border-white/80',
              style: { background: langTopic.theme.iconGradient }
            },
            el(langTopic.icon, { className: 'w-7 h-7' })
          ),
          el(
            'div',
            null,
            el(
              'span',
              {
                style: { color: langTopic.theme.labelColor },
                className: 'text-xs font-extrabold uppercase tracking-wider'
              },
              langTopic.badge
            ),
            el(
              'h3',
              {
                style: { backgroundImage: langTopic.theme.headingGradient },
                className: 'text-2xl sm:text-3xl frutiger-aero-heading'
              },
              `${langTopic.name} — Laboratorio Interactivo`
            )
          )
        ),
        el(
          'div',
          { className: 'grid grid-cols-1 sm:grid-cols-2 gap-4 text-sm' },
          el(
            'div',
            { className: 'bg-white/95 rounded-2xl p-4 border border-white shadow-sm' },
            el(
              'span',
              {
                style: { color: langTopic.theme.labelColor },
                className: 'block text-xs font-extrabold uppercase mb-1'
              },
              '¿Qué hace?'
            ),
            el('p', { className: 'text-[#334155] leading-relaxed' }, langTopic.whatItDoes)
          ),
          el(
            'div',
            {
              style: { backgroundColor: langTopic.theme.cardTintBg },
              className: 'rounded-2xl p-4 border border-white shadow-sm'
            },
            el(
              'span',
              {
                style: { color: langTopic.theme.labelColor },
                className: 'block text-xs font-extrabold uppercase mb-1'
              },
              '¿Para qué sirve?'
            ),
            el('p', { className: 'text-[#334155] leading-relaxed' }, langTopic.whatItIsFor)
          )
        ),
        el(
          'div',
          { className: 'aero-metal-surface rounded-2xl p-4 space-y-1.5' },
          el(
            'span',
            {
              style: { color: langTopic.theme.labelColor },
              className: 'inline-flex items-center gap-1.5 text-xs font-extrabold uppercase'
            },
            el(Sparkles, { className: 'w-4 h-4' }),
            'Domando Herramientas de Inteligencia Artificial'
          ),
          el('p', { className: 'text-xs sm:text-sm text-[#334155] leading-relaxed' }, langTopic.aiSynergy),
          el(
            'p',
            {
              style: { color: langTopic.theme.labelColor },
              className: 'text-xs font-bold pt-1'
            },
            `Proyecto en el club: ${langTopic.projectExample}`
          )
        ),
        // Terminal de código
        el(
          'div',
          { className: 'rounded-2xl overflow-hidden border border-[#94A3B8] bg-[#0F172A] text-slate-100 shadow-inner' },
          el(
            'div',
            { className: 'px-4 py-2 bg-[#1E293B] flex items-center justify-between text-xs' },
            el(
              'span',
              {
                style: { color: langTopic.secondary },
                className: 'font-mono font-bold'
              },
              `${langTopic.exeName} — Código Fuente`
            ),
            el(
              'button',
              {
                type: 'button',
                onClick: () => handleCopyCode(langTopic.codeSnippet),
                className:
                  'inline-flex items-center gap-1.5 px-3 py-1 rounded-lg bg-white/10 hover:bg-white/20 text-white font-bold transition-colors cursor-pointer'
              },
              copiedCode
                ? [el(Check, { key: 'i', className: 'w-3.5 h-3.5 text-emerald-400' }), el('span', { key: 't' }, 'Copiado')]
                : [el(Copy, { key: 'i', className: 'w-3.5 h-3.5' }), el('span', { key: 't' }, 'Copiar código')]
            )
          ),
          el(
            'pre',
            { className: 'p-4 text-xs sm:text-sm font-mono overflow-x-auto leading-relaxed text-slate-100' },
            el('code', null, langTopic.codeSnippet)
          )
        )
      );
    } else if (maximizedWindowId === 'spike') {
      modalContent = el(
        'div',
        { className: 'space-y-4 text-sm text-[#334155]' },
        el(
          'h3',
          {
            style: { backgroundImage: SPIKE_THEME.headingGradient },
            className: 'text-2xl font-black frutiger-aero-heading'
          },
          'LEGO SPIKE PRIME — Arquitectura del Kit'
        ),
        el(SpikePrimeDiagram, {
          activePartId: activeSpikePart,
          onSelectPart: setActiveSpikePart
        }),
        el(
          'div',
          {
            style: { backgroundColor: SPIKE_THEME.cardTintBg },
            className: 'rounded-2xl p-4 border border-white'
          },
          el(
            'h4',
            { style: { color: SPIKE_THEME.labelColor }, className: 'font-extrabold text-base mb-1' },
            currentSpikePart.name
          ),
          el('p', { className: 'text-xs sm:text-sm leading-relaxed' }, currentSpikePart.description)
        )
      );
    } else if (maximizedWindowId === 'arduino') {
      modalContent = el(
        'div',
        { className: 'space-y-4 text-sm text-[#334155]' },
        el(
          'h3',
          {
            style: { backgroundImage: ARDUINO_THEME.headingGradient },
            className: 'text-2xl font-black frutiger-aero-heading'
          },
          'Robótica Avanzada ARDUINO — Laboratorio Electrónico'
        ),
        el(ArduinoDiagram, {
          activePartId: activeArduinoPart,
          onSelectPart: setActiveArduinoPart
        }),
        el(
          'div',
          {
            style: { backgroundColor: ARDUINO_THEME.cardTintBg },
            className: 'rounded-2xl p-4 border border-white'
          },
          el(
            'h4',
            { style: { color: ARDUINO_THEME.labelColor }, className: 'font-extrabold text-base mb-1' },
            currentArduinoPart.name
          ),
          el('p', { className: 'text-xs sm:text-sm leading-relaxed' }, currentArduinoPart.description)
        )
      );
    } else {
      modalContent = el(
        'div',
        { className: 'space-y-4 text-sm text-[#334155]' },
        el(
          'h3',
          { className: 'text-2xl font-black frutiger-aero-heading' },
          `${catalogItem.exeName} — Vista Ampliada`
        ),
        el(
          'p',
          { className: 'leading-relaxed' },
          'Has maximizado este módulo de TECH MASTERS. Puedes interactuar directamente con todos sus diagramas, controles y herramientas en la pantalla principal o restaurar la vista estándar.'
        ),
        el(
          'div',
          { className: 'aero-metal-surface rounded-2xl p-4 space-y-2' },
          el('p', { className: 'font-bold text-[#0052A3]' }, 'Resumen Rápido del Club TECH MASTERS:'),
          el(
            'p',
            null,
            '• Estudiantes de 11 a 16 años aprendiendo programación (Python, HTML, CSS, JavaScript), Inteligencia Artificial, robótica LEGO SPIKE PRIME y Arduino.'
          ),
          el(
            'p',
            null,
            '• Construcción de proyectos reales y participación en concursos nacionales e internacionales.'
          )
        ),
        el(
          'div',
          { className: 'flex justify-end' },
          el(
            'button',
            {
              type: 'button',
              onClick: () => {
                const targetSec = catalogItem.sectionId;
                const targetId = catalogItem.id;
                setMaximizedWindowId(null);
                restoreAndFocusWindow(targetId, targetSec);
              },
              className: 'aero-btn-primary px-5 py-2.5 rounded-xl text-white font-bold text-xs cursor-pointer'
            },
            'Ir al Módulo Interactivo'
          )
        )
      );
    }

    return el(
      'div',
      {
        className: 'fixed inset-0 z-50 flex items-center justify-center p-4 bg-[#0F172A]/50 backdrop-blur-sm',
        onClick: () => setMaximizedWindowId(null)
      },
      el(
        'div',
        {
          style: modalTheme
            ? {
                background: modalTheme.windowBg,
                '--win-ring': modalTheme.hoverRingColor,
                '--win-shadow': modalTheme.hoverShadowColor
              }
            : undefined,
          className: 'win-aero-window rounded-2xl max-w-2xl w-full overflow-hidden shadow-2xl',
          onClick: (ev) => ev.stopPropagation()
        },
        // Barra de título Windows Aero del Modal
        el(
          'div',
          {
            style: modalTheme ? { background: modalTheme.titlebarGradient } : undefined,
            className: 'win-aero-titlebar px-4 py-2.5 flex items-center justify-between border-b border-white'
          },
          el(
            'div',
            { className: 'flex items-center gap-2' },
            el(AppWindow, {
              style: modalTheme ? { color: modalTheme.labelColor } : undefined,
              className: 'w-4 h-4 text-[#0078D7]'
            }),
            el(
              'span',
              { className: 'win-aero-title-label text-xs sm:text-sm font-extrabold text-[#0F172A]' },
              `${catalogItem.exeName} [Ventana Maximizada]`
            )
          ),
          el(
            'div',
            { className: 'flex items-center gap-1' },
            el(
              'button',
              {
                type: 'button',
                onClick: () => setMaximizedWindowId(null),
                title: 'Restaurar tamaño',
                className:
                  'win-caption-btn win-caption-max w-7 h-6 rounded-md flex items-center justify-center text-[#0F172A] font-black text-xs cursor-pointer'
              },
              '❐'
            ),
            el(
              'button',
              {
                type: 'button',
                onClick: () => setMaximizedWindowId(null),
                title: 'Cerrar ventana emergente',
                className:
                  'win-caption-btn win-caption-close w-8 h-6 rounded-md flex items-center justify-center text-white font-black text-xs cursor-pointer'
              },
              '✕'
            )
          )
        ),
        el('div', { className: 'p-6 sm:p-7 bg-white/85 max-h-[80vh] overflow-y-auto' }, modalContent),
        el(
          'div',
          {
            style: modalTheme
              ? {
                  background: modalTheme.statusbarBg,
                  borderTopColor: modalTheme.statusbarBorder
                }
              : undefined,
            className:
              'win-aero-statusbar px-4 py-1.5 flex items-center justify-between text-[11px] font-semibold text-[#334155]'
          },
          el('span', null, 'Modo Vista Ampliada • Windows Aero Compositor'),
          el('span', { className: 'font-mono text-[#64748B]' }, '◢')
        )
      )
    );
  };

  return el(
    'div',
    {
      className:
        'min-h-screen relative overflow-x-hidden text-[#0F172A] bg-gradient-to-br from-[#38BDF8]/35 via-[#E0F2FE] to-[#CBD5E1] selection:bg-[#00B4FF] selection:text-white'
    },
    // =========================================================================
    // FONDO ATMOSFÉRICO FRUTIGER AERO ROBÓTICO
    // =========================================================================
    el(
      'div',
      { className: 'fixed inset-0 pointer-events-none z-0 overflow-hidden' },
      el('div', {
        className:
          'absolute -top-32 -left-32 w-[540px] h-[540px] rounded-full bg-gradient-to-br from-[#00B4FF]/40 via-[#38BDF8]/25 to-transparent blur-3xl'
      }),
      el('div', {
        className:
          'absolute top-1/4 -right-36 w-[580px] h-[580px] rounded-full bg-gradient-to-tl from-[#0078D7]/30 via-[#BAE6FD]/50 to-white/70 blur-3xl'
      }),
      el('div', {
        className:
          'absolute -bottom-36 left-1/4 w-[500px] h-[500px] rounded-full bg-gradient-to-tr from-[#94A3B8]/35 via-[#E0F2FE]/55 to-white/75 blur-3xl'
      }),
      // Ondas de luz glossy superiores
      el(
        'svg',
        {
          viewBox: '0 0 1440 320',
          preserveAspectRatio: 'none',
          className: 'absolute top-0 inset-x-0 w-full h-72 opacity-60'
        },
        el('path', {
          fill: '#FFFFFF',
          fillOpacity: '0.55',
          d: 'M0,128L80,138.7C160,149,320,171,480,165.3C640,160,800,128,960,122.7C1120,117,1280,139,1360,149.3L1440,160L1440,0L1360,0C1280,0,1120,0,960,0C800,0,640,0,480,0C320,0,160,0,80,0L0,0Z'
        })
      ),
      // Cuadrícula de circuitos robóticos en gris metálico
      el(
        'svg',
        { className: 'w-full h-full opacity-[0.3]', xmlns: 'http://www.w3.org/2000/svg' },
        el(
          'defs',
          null,
          el(
            'pattern',
            { id: 'aeroTechGrid', width: '48', height: '48', patternUnits: 'userSpaceOnUse' },
            el('path', { d: 'M 48 0 L 0 0 0 48', fill: 'none', stroke: '#94A3B8', strokeWidth: '0.75' }),
            el('circle', { cx: '0', cy: '0', r: '1.6', fill: '#00B4FF' })
          )
        ),
        el('rect', { width: '100%', height: '100%', fill: 'url(#aeroTechGrid)' })
      ),
      // Burbujas translúcidas flotantes con brillo especular
      el(
        'div',
        {
          className:
            'hidden md:block absolute top-28 right-[10%] w-24 h-24 rounded-full bg-gradient-to-b from-white/95 via-[#BAE6FD]/45 to-[#00B4FF]/35 border border-white shadow-[0_12px_30px_rgba(0,180,255,0.24)] aero-float-slow'
        },
        el('div', { className: 'w-10 h-5 rounded-full bg-white/90 blur-[1px] mt-2.5 ml-4 -rotate-12' })
      ),
      el(
        'div',
        {
          className:
            'hidden lg:block absolute top-[52%] left-[5%] w-20 h-20 rounded-full bg-gradient-to-b from-white/95 via-[#E2E8F0]/55 to-[#0078D7]/30 border border-white shadow-[0_10px_25px_rgba(0,120,215,0.2)] aero-float-reverse'
        },
        el('div', { className: 'w-8 h-4 rounded-full bg-white/90 blur-[1px] mt-2 ml-3.5 -rotate-12' })
      )
    ),

    // =========================================================================
    // ENCABEZADO SUPERIOR ESTILO WINDOWS AERO GLASS BAR
    // =========================================================================
    el(
      'header',
      { className: 'sticky top-3 z-40 px-4 sm:px-6 lg:px-8 max-w-7xl mx-auto' },
      el(
        'div',
        { className: 'win-aero-window rounded-2xl px-4 sm:px-6 py-3 flex items-center justify-between gap-4' },
        // Logotipo TECH MASTERS con letras Frutiger Aero
        el(
          'a',
          { href: '#que-es', className: 'flex items-center gap-3 group' },
          el(
            'div',
            { className: 'w-11 h-11 rounded-2xl aero-btn-primary flex items-center justify-center text-white shadow-md' },
            el(Bot, { className: 'w-6 h-6' })
          ),
          el(
            'div',
            null,
            el(
              'span',
              { className: 'frutiger-aero-wordmark text-xl sm:text-2xl leading-none block' },
              'TECH MASTERS'
            ),
            el(
              'span',
              { className: 'block text-[10px] font-extrabold uppercase tracking-widest text-[#334155] mt-0.5' },
              'Windows Aero Robotics OS • 11-16 Años'
            )
          )
        ),
        // Navegación rápida
        el(
          'div',
          { className: 'hidden lg:flex items-center gap-1.5' },
          [
            { href: '#que-es', label: '¿Qué es?' },
            { href: '#que-ensenamos', label: '¿Qué Enseñamos?' },
            { href: '#division-robotica', label: 'Robótica' },
            { href: '#acceso-qr', label: 'Código QR' }
          ].map((navItem) =>
            el(
              'a',
              {
                key: navItem.href,
                href: navItem.href,
                className:
                  'px-3.5 py-2 rounded-xl text-sm font-bold text-[#1E293B] hover:text-[#0078D7] hover:bg-white/90 border border-transparent hover:border-white transition-all'
              },
              navItem.label
            )
          )
        ),
        // Indicador Pure JS + Botón Restaurar Ventanas si hay cerradas
        el(
          'div',
          { className: 'flex items-center gap-2' },
          anyWindowHidden
            ? el(
                'button',
                {
                  type: 'button',
                  onClick: restoreAllWindows,
                  className:
                    'aero-btn-primary px-3 py-1.5 rounded-xl text-white text-xs font-bold inline-flex items-center gap-1.5 cursor-pointer'
                },
                el(RotateCcw, { className: 'w-3.5 h-3.5' }),
                el('span', null, 'Restaurar Ventanas')
              )
            : null,
          el(
            'span',
            {
              className:
                'inline-flex items-center gap-1.5 px-3 py-1.5 rounded-full text-xs font-extrabold text-[#0052A3] bg-gradient-to-b from-white to-[#E0F2FE] border border-white shadow-sm'
            },
            el('span', { className: 'w-2 h-2 rounded-full bg-[#06B6D4] animate-pulse' }),
            el('span', { className: 'hidden sm:inline' }, 'React.createElement • Zero-HTML'),
            el('span', { className: 'sm:hidden' }, 'Pure JS')
          )
        )
      )
    ),

    // =========================================================================
    // CONTENIDO PRINCIPAL CON VENTANAS POP-UP DE WINDOWS AERO
    // =========================================================================
    el(
      'main',
      { className: 'relative z-10 max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 pt-7 pb-28 space-y-20' },

      // -----------------------------------------------------------------------
      // 1. VENTANA POP-UP PRINCIPAL: 'TECH_MASTERS_Inicio.exe' (¿QUÉ ES?)
      // -----------------------------------------------------------------------
      el(
        'section',
        { id: 'que-es', className: 'scroll-mt-24' },
        el(
          AeroWindow,
          {
            id: 'inicio',
            exeName: 'TECH_MASTERS_Inicio.exe',
            subtitle: 'Portal Oficial del Club',
            icon: Monitor,
            statusText: 'Estado: En línea | Edad: 11-16 años | Arquitectura: 100% React.createElement',
            isMinimized: !!minimizedMap.inicio,
            isClosed: !!closedMap.inicio,
            onMinimize: () => toggleMinimize('inicio'),
            onMaximize: () => setMaximizedWindowId('inicio'),
            onClose: () => closeWindow('inicio')
          },
          el(
            'div',
            { className: 'space-y-8' },
            el(
              'div',
              { className: 'grid grid-cols-1 lg:grid-cols-12 gap-8 items-center' },
              // Columna de texto
              el(
                'div',
                { className: 'lg:col-span-7 space-y-5' },
                el(
                  'div',
                  {
                    className:
                      'inline-flex items-center gap-2 px-4 py-1.5 rounded-full bg-white/95 border border-[#38BDF8]/50 shadow-sm'
                  },
                  el(Sparkles, { className: 'w-4 h-4 text-[#00B4FF]' }),
                  el(
                    'span',
                    { className: 'text-xs sm:text-sm font-extrabold text-[#0078D7]' },
                    'Club de Tecnología, Robótica e Inteligencia Artificial'
                  )
                ),
                el(
                  'h1',
                  { className: 'text-4xl sm:text-5xl lg:text-6xl font-black tracking-tight leading-[1.08]' },
                  el('span', { className: 'block text-[#0F172A]' }, '¿Qué es'),
                  el('span', { className: 'frutiger-aero-wordmark block mt-1' }, 'TECH MASTERS?')
                ),
                el(
                  'p',
                  { className: 'text-base sm:text-lg text-[#1E293B] leading-relaxed font-semibold' },
                  'TECH MASTERS es un club tecnológico donde estudiantes de ',
                  el('span', { className: 'text-[#0078D7] font-extrabold' }, '11 a 16 años'),
                  ' aprenden a programar, construir robots reales, desarrollar proyectos creativos en equipo y participar en concursos nacionales e internacionales, mientras dominan herramientas de ',
                  el('span', { className: 'text-[#0078D7] font-extrabold' }, 'Inteligencia Artificial (IA)'),
                  ' y crean páginas web profesionales.'
                ),
                el(
                  'p',
                  { className: 'text-sm sm:text-base text-[#475569] leading-relaxed' },
                  'Combinamos ingeniería mecánica, electrónica con microcontroladores y desarrollo web moderno para transformar la curiosidad juvenil en habilidades tecnológicas de alto impacto.'
                ),
                el(
                  'div',
                  { className: 'flex flex-wrap items-center gap-3.5 pt-1' },
                  el(
                    'a',
                    {
                      href: '#que-ensenamos',
                      className:
                        'aero-btn-primary px-6 py-3.5 rounded-2xl text-white font-extrabold text-sm sm:text-base inline-flex items-center gap-2'
                    },
                    el('span', null, 'Explorar Qué Enseñamos'),
                    el(ChevronRight, { className: 'w-5 h-5' })
                  ),
                  el(
                    'a',
                    {
                      href: '#division-robotica',
                      className:
                        'px-6 py-3.5 rounded-2xl font-extrabold text-sm sm:text-base text-[#0052A3] aero-metal-surface hover:border-[#00B4FF] hover:text-[#0078D7] transition-all inline-flex items-center gap-2'
                    },
                    el(Cpu, { className: 'w-5 h-5 text-[#00B4FF]' }),
                    el('span', null, 'Ver Robótica')
                  )
                )
              ),
              // Columna Ilustración SVG Frutiger Aero
              el(
                'div',
                { className: 'lg:col-span-5' },
                el(RoboticCoreIllustration, {
                  scanMode,
                  onToggleScan: () => setScanMode((prev) => !prev)
                })
              )
            ),
            // 4 Sub-módulos clave del club
            el(
              'div',
              { className: 'grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-4 pt-6 border-t border-[#CBD5E1]/80' },
              [
                {
                  icon: Users,
                  title: 'Edades 11 a 16 años',
                  desc: 'Mentoría personalizada por niveles y trabajo colaborativo en equipo.'
                },
                {
                  icon: Sparkles,
                  title: 'Domina la IA y la Web',
                  desc: 'Aprende a usar herramientas de IA y diseñar sitios web profesionales.'
                },
                {
                  icon: Bot,
                  title: 'Robots Reales',
                  desc: 'Construcción mecánica y electrónica con LEGO SPIKE PRIME y Arduino.'
                },
                {
                  icon: Trophy,
                  title: 'Concursos y Torneos',
                  desc: 'Competencias nacionales e internacionales con proyectos funcionales.'
                }
              ].map((item) =>
                el(
                  'div',
                  {
                    key: item.title,
                    className: 'aero-metal-surface rounded-2xl p-4 flex flex-col justify-between'
                  },
                  el(
                    'div',
                    { className: 'flex items-center gap-3 mb-2' },
                    el(
                      'div',
                      {
                        className:
                          'w-9 h-9 rounded-xl bg-gradient-to-br from-[#38BDF8] to-[#0078D7] text-white flex items-center justify-center shadow-sm shrink-0'
                      },
                      el(item.icon, { className: 'w-5 h-5' })
                    ),
                    el('h2', { className: 'font-extrabold text-[#0F172A] text-sm sm:text-base' }, item.title)
                  ),
                  el('p', { className: 'text-xs text-[#475569] leading-relaxed' }, item.desc)
                )
              )
            )
          )
        )
      ),

      // -----------------------------------------------------------------------
      // 2. SECCIÓN '¿QUÉ ENSEÑAMOS?' (6 VENTANAS POP-UP DE WINDOWS AERO CON COLORES DISTINTIVOS)
      // -----------------------------------------------------------------------
      el(
        'section',
        { id: 'que-ensenamos', className: 'scroll-mt-24 space-y-10' },
        el(
          'div',
          { className: 'text-center max-w-3xl mx-auto space-y-2.5' },
          el(
            'div',
            {
              className:
                'inline-flex items-center gap-2 px-4 py-1 rounded-full bg-white/90 border border-white text-xs font-extrabold text-[#0078D7] shadow-sm'
            },
            el(Code2, { className: 'w-4 h-4 text-[#00B4FF]' }),
            el('span', null, '6 Módulos Interactivos • Programación, Web, IA y Robótica')
          ),
          el(
            'h2',
            { className: 'text-3xl sm:text-4xl lg:text-5xl frutiger-aero-heading tracking-tight' },
            '¿Qué Enseñamos?'
          ),
          el(
            'p',
            { className: 'text-sm sm:text-base text-[#334155] font-medium' },
            'Cada especialidad cuenta con su propia ventana cristalina Windows Aero de color distintivo: minimízala, ciérrala hacia la barra de tareas o maximízala para explorar su laboratorio.'
          )
        ),

        // Fila 1: Las 4 ventanas de Lenguajes y Desarrollo Web (Esmeralda, Coral, Dorado Solar, Zafiro)
        el(
          'div',
          { className: 'grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6' },
          PROGRAMMING_TOPICS.map((topic) =>
            el(
              AeroWindow,
              {
                key: topic.id,
                id: topic.id,
                exeName: topic.exeName,
                icon: topic.icon,
                statusText: topic.statusBar,
                theme: topic.theme,
                isMinimized: !!minimizedMap[topic.id],
                isClosed: !!closedMap[topic.id],
                onMinimize: () => toggleMinimize(topic.id),
                onMaximize: () => {
                  setMaximizedWindowId(topic.id);
                  setCopiedCode(false);
                },
                onClose: () => closeWindow(topic.id)
              },
              el(
                'div',
                { className: 'space-y-4' },
                el(
                  'div',
                  { className: 'flex items-center justify-between gap-2' },
                  el(
                    'h3',
                    {
                      style: { backgroundImage: topic.theme.headingGradient },
                      className: 'text-2xl font-black frutiger-aero-heading'
                    },
                    topic.name
                  ),
                  el(
                    'span',
                    {
                      style: {
                        backgroundColor: topic.theme.badgeBg,
                        color: topic.theme.badgeText
                      },
                      className:
                        'px-2.5 py-1 rounded-full text-[11px] font-extrabold border border-white shadow-xs shrink-0'
                    },
                    topic.badge
                  )
                ),
                el(
                  'div',
                  { className: 'p-3 rounded-xl bg-white/92 border border-white shadow-xs' },
                  el(
                    'span',
                    {
                      style: { color: topic.theme.labelColor },
                      className: 'block text-[11px] font-extrabold uppercase tracking-wider mb-1'
                    },
                    '¿Qué hace?'
                  ),
                  el('p', { className: 'text-xs sm:text-sm text-[#334155] leading-relaxed' }, topic.whatItDoes)
                ),
                el(
                  'div',
                  {
                    style: { backgroundColor: topic.theme.cardTintBg },
                    className: 'p-3 rounded-xl border border-white'
                  },
                  el(
                    'span',
                    {
                      style: { color: topic.theme.labelColor },
                      className: 'block text-[11px] font-extrabold uppercase tracking-wider mb-1'
                    },
                    '¿Para qué sirve?'
                  ),
                  el('p', { className: 'text-xs sm:text-sm text-[#334155] leading-relaxed' }, topic.whatItIsFor)
                )
              ),
              el(
                'button',
                {
                  type: 'button',
                  onClick: () => {
                    setMaximizedWindowId(topic.id);
                    setCopiedCode(false);
                  },
                  style: {
                    background: topic.theme.buttonGradient,
                    boxShadow: topic.theme.buttonShadow
                  },
                  className:
                    'mt-5 w-full aero-btn-primary py-2.5 px-4 rounded-xl text-white text-xs font-extrabold flex items-center justify-center gap-1.5 cursor-pointer'
                },
                el('span', null, 'Abrir Pop-Up de Código'),
                el(ChevronRight, { className: 'w-4 h-4' })
              )
            )
          )
        ),

        // Fila 2: Las 2 ventanas de Robótica (Violeta Cibernético y Carmesí Robótico)
        el(
          'div',
          { id: 'division-robotica', className: 'scroll-mt-24 pt-2 space-y-6' },
          el(
            'div',
            { className: 'flex items-center justify-center gap-3' },
            el('div', { className: 'h-px flex-1 max-w-28 bg-gradient-to-r from-transparent to-[#94A3B8]/60' }),
            el(
              'span',
              {
                className:
                  'inline-flex items-center gap-2 px-4 py-1.5 rounded-full bg-white/90 border border-white text-xs font-extrabold text-[#1E293B] shadow-sm'
              },
              el(CircuitBoard, { className: 'w-4 h-4 text-[#7C3AED]' }),
              el('span', null, 'División de Robótica • Diagramas Interactivos')
            ),
            el('div', { className: 'h-px flex-1 max-w-28 bg-gradient-to-l from-transparent to-[#94A3B8]/60' })
          ),

          el(
            'div',
            { className: 'grid grid-cols-1 lg:grid-cols-2 gap-8' },
            // VENTANA 5: LEGO_SpikePrime.exe (Violeta / Índigo Cibernético #7C3AED / #8B5CF6)
            el(
              AeroWindow,
              {
                id: 'spike',
                exeName: 'LEGO_SpikePrime.exe',
                subtitle: 'Robótica de Competencia',
                icon: Layers,
                statusText: 'Hardware: Hub 5x5 + Motores + Sensores | Tema: Violeta Cibernético',
                theme: SPIKE_THEME,
                isMinimized: !!minimizedMap.spike,
                isClosed: !!closedMap.spike,
                onMinimize: () => toggleMinimize('spike'),
                onMaximize: () => setMaximizedWindowId('spike'),
                onClose: () => closeWindow('spike')
              },
              el(
                'div',
                { className: 'space-y-4' },
                el(
                  'div',
                  { className: 'flex items-center justify-between gap-2' },
                  el(
                    'h3',
                    {
                      style: { backgroundImage: SPIKE_THEME.headingGradient },
                      className: 'text-2xl font-black frutiger-aero-heading'
                    },
                    'Robótica LEGO SPIKE PRIME'
                  ),
                  el(
                    'span',
                    {
                      style: {
                        backgroundColor: SPIKE_THEME.badgeBg,
                        color: SPIKE_THEME.badgeText
                      },
                      className: 'px-2.5 py-1 rounded-full text-[11px] font-extrabold border border-white'
                    },
                    'Índigo Cibernético'
                  )
                ),
                el(
                  'div',
                  { className: 'flex gap-2 p-1.5 rounded-2xl bg-white/85 border border-white' },
                  el(
                    'button',
                    {
                      type: 'button',
                      onClick: () => setSpikeTab('parts'),
                      style:
                        spikeTab === 'parts'
                          ? {
                              background: SPIKE_THEME.buttonGradient,
                              boxShadow: SPIKE_THEME.buttonShadow
                            }
                          : undefined,
                      className: `flex-1 py-2 px-3 rounded-xl text-xs sm:text-sm font-extrabold transition-all cursor-pointer ${
                        spikeTab === 'parts'
                          ? 'aero-btn-primary text-white'
                          : 'text-[#475569] hover:text-[#7C3AED]'
                      }`
                    },
                    'Partes del Kit (Diagrama)'
                  ),
                  el(
                    'button',
                    {
                      type: 'button',
                      onClick: () => setSpikeTab('capabilities'),
                      style:
                        spikeTab === 'capabilities'
                          ? {
                              background: SPIKE_THEME.buttonGradient,
                              boxShadow: SPIKE_THEME.buttonShadow
                            }
                          : undefined,
                      className: `flex-1 py-2 px-3 rounded-xl text-xs sm:text-sm font-extrabold transition-all cursor-pointer ${
                        spikeTab === 'capabilities'
                          ? 'aero-btn-primary text-white'
                          : 'text-[#475569] hover:text-[#7C3AED]'
                      }`
                    },
                    '¿Qué se puede construir?'
                  )
                ),
                el(SpikePrimeDiagram, {
                  activePartId: activeSpikePart,
                  onSelectPart: (partId) => {
                    setActiveSpikePart(partId);
                    setSpikeTab('parts');
                  }
                }),
                spikeTab === 'parts'
                  ? el(
                      'div',
                      { className: 'space-y-3' },
                      el(
                        'div',
                        { className: 'flex flex-wrap gap-1.5' },
                        SPIKE_PARTS.map((part) =>
                          el(
                            'button',
                            {
                              key: part.id,
                              type: 'button',
                              onClick: () => setActiveSpikePart(part.id),
                              style:
                                activeSpikePart === part.id
                                  ? {
                                      backgroundColor: '#7C3AED',
                                      borderColor: '#7C3AED',
                                      color: '#FFFFFF'
                                    }
                                  : undefined,
                              className: `px-3 py-1.5 rounded-xl text-xs font-extrabold transition-all cursor-pointer border ${
                                activeSpikePart === part.id
                                  ? 'shadow-sm'
                                  : 'bg-white/95 text-[#334155] border-white hover:border-[#8B5CF6]'
                              }`
                            },
                            part.tag
                          )
                        )
                      ),
                      el(
                        'div',
                        {
                          style: { backgroundColor: SPIKE_THEME.cardTintBg },
                          className: 'rounded-2xl p-4 border border-white shadow-xs'
                        },
                        el(
                          'div',
                          { className: 'flex items-center justify-between mb-1 gap-2' },
                          el(
                            'h4',
                            { style: { color: SPIKE_THEME.labelColor }, className: 'font-extrabold text-base' },
                            currentSpikePart.name
                          ),
                          el(
                            'span',
                            {
                              style: {
                                backgroundColor: SPIKE_THEME.badgeBg,
                                color: SPIKE_THEME.badgeText
                              },
                              className: 'text-[11px] font-bold px-2.5 py-0.5 rounded-full border border-white shrink-0'
                            },
                            currentSpikePart.tag
                          )
                        ),
                        el('p', { className: 'text-xs sm:text-sm text-[#334155] leading-relaxed' }, currentSpikePart.description)
                      )
                    )
                  : el(
                      'div',
                      {
                        style: { backgroundColor: SPIKE_THEME.cardTintBg },
                        className: 'rounded-2xl p-4 border border-white space-y-2.5'
                      },
                      el(
                        'h4',
                        { style: { color: SPIKE_THEME.labelColor }, className: 'font-extrabold text-base' },
                        '¿Qué se puede construir y lograr con este kit?'
                      ),
                      el(
                        'ul',
                        { className: 'space-y-2 text-xs sm:text-sm text-[#334155]' },
                        el(
                          'li',
                          { className: 'flex items-start gap-2' },
                          el(Check, { className: 'w-4 h-4 text-[#8B5CF6] shrink-0 mt-0.5' }),
                          el(
                            'span',
                            null,
                            el('strong', null, 'Robots autónomos de competición'),
                            ' capaces de resolver misiones cronometradas en torneos internacionales.'
                          )
                        ),
                        el(
                          'li',
                          { className: 'flex items-start gap-2' },
                          el(Check, { className: 'w-4 h-4 text-[#8B5CF6] shrink-0 mt-0.5' }),
                          el(
                            'span',
                            null,
                            el('strong', null, 'Brazos mecánicos articulados y pinzas de precisión'),
                            ' controlados por giroscopio y sensores ópticos.'
                          )
                        ),
                        el(
                          'li',
                          { className: 'flex items-start gap-2' },
                          el(Check, { className: 'w-4 h-4 text-[#8B5CF6] shrink-0 mt-0.5' }),
                          el(
                            'span',
                            null,
                            el('strong', null, 'Sistemas clasificadores por color y seguidores de línea'),
                            ' con algoritmos inteligentes.'
                          )
                        )
                      )
                    )
              )
            ),

            // VENTANA 6: Arduino_Robotica.exe (Carmesí / Magenta Robótico #E11D48 / #F43F5E)
            el(
              AeroWindow,
              {
                id: 'arduino',
                exeName: 'Arduino_Robotica.exe',
                subtitle: 'Electrónica & C++',
                icon: Cpu,
                statusText: 'Hardware: Arduino UNO + HC-SR04 + Servos | Tema: Carmesí Robótico',
                theme: ARDUINO_THEME,
                isMinimized: !!minimizedMap.arduino,
                isClosed: !!closedMap.arduino,
                onMinimize: () => toggleMinimize('arduino'),
                onMaximize: () => setMaximizedWindowId('arduino'),
                onClose: () => closeWindow('arduino')
              },
              el(
                'div',
                { className: 'space-y-4' },
                el(
                  'div',
                  { className: 'flex items-center justify-between gap-2' },
                  el(
                    'h3',
                    {
                      style: { backgroundImage: ARDUINO_THEME.headingGradient },
                      className: 'text-2xl font-black frutiger-aero-heading'
                    },
                    'Robótica Avanzada (ARDUINO)'
                  ),
                  el(
                    'span',
                    {
                      style: {
                        backgroundColor: ARDUINO_THEME.badgeBg,
                        color: ARDUINO_THEME.badgeText
                      },
                      className: 'px-2.5 py-1 rounded-full text-[11px] font-extrabold border border-white'
                    },
                    'Carmesí Robótico'
                  )
                ),
                el(
                  'div',
                  { className: 'flex gap-1.5 p-1.5 rounded-2xl bg-white/85 border border-white' },
                  [
                    { id: 'parts', label: 'Partes (Diagrama)' },
                    { id: 'what', label: '¿Qué hace?' },
                    { id: 'learn', label: '¿Qué aprendes?' }
                  ].map((tab) =>
                    el(
                      'button',
                      {
                        key: tab.id,
                        type: 'button',
                        onClick: () => setArduinoTab(tab.id),
                        style:
                          arduinoTab === tab.id
                            ? {
                                background: ARDUINO_THEME.buttonGradient,
                                boxShadow: ARDUINO_THEME.buttonShadow
                              }
                            : undefined,
                        className: `flex-1 py-2 px-2.5 rounded-xl text-xs font-extrabold transition-all cursor-pointer ${
                          arduinoTab === tab.id
                            ? 'aero-btn-primary text-white'
                            : 'text-[#475569] hover:text-[#E11D48]'
                        }`
                      },
                      tab.label
                    )
                  )
                ),
                el(ArduinoDiagram, {
                  activePartId: activeArduinoPart,
                  onSelectPart: (partId) => {
                    setActiveArduinoPart(partId);
                    setArduinoTab('parts');
                  }
                }),
                arduinoTab === 'parts'
                  ? el(
                      'div',
                      { className: 'space-y-3' },
                      el(
                        'div',
                        { className: 'flex flex-wrap gap-1.5' },
                        ARDUINO_PARTS.map((part) =>
                          el(
                            'button',
                            {
                              key: part.id,
                              type: 'button',
                              onClick: () => setActiveArduinoPart(part.id),
                              style:
                                activeArduinoPart === part.id
                                  ? {
                                      backgroundColor: '#E11D48',
                                      borderColor: '#E11D48',
                                      color: '#FFFFFF'
                                    }
                                  : undefined,
                              className: `px-3 py-1.5 rounded-xl text-xs font-extrabold transition-all cursor-pointer border ${
                                activeArduinoPart === part.id
                                  ? 'shadow-sm'
                                  : 'bg-white/95 text-[#334155] border-white hover:border-[#F43F5E]'
                              }`
                            },
                            part.tag
                          )
                        )
                      ),
                      el(
                        'div',
                        {
                          style: { backgroundColor: ARDUINO_THEME.cardTintBg },
                          className: 'rounded-2xl p-4 border border-white shadow-xs'
                        },
                        el(
                          'div',
                          { className: 'flex items-center justify-between mb-1 gap-2' },
                          el(
                            'h4',
                            { style: { color: ARDUINO_THEME.labelColor }, className: 'font-extrabold text-base' },
                            currentArduinoPart.name
                          ),
                          el(
                            'span',
                            {
                              style: {
                                backgroundColor: ARDUINO_THEME.badgeBg,
                                color: ARDUINO_THEME.badgeText
                              },
                              className: 'text-[11px] font-bold px-2.5 py-0.5 rounded-full border border-white shrink-0'
                            },
                            currentArduinoPart.tag
                          )
                        ),
                        el('p', { className: 'text-xs sm:text-sm text-[#334155] leading-relaxed' }, currentArduinoPart.description)
                      )
                    )
                  : null,
                arduinoTab === 'what'
                  ? el(
                      'div',
                      {
                        style: { backgroundColor: ARDUINO_THEME.cardTintBg },
                        className: 'rounded-2xl p-4 border border-white space-y-2'
                      },
                      el(
                        'h4',
                        { style: { color: ARDUINO_THEME.labelColor }, className: 'font-extrabold text-base' },
                        '¿Qué hace Arduino?'
                      ),
                      el(
                        'p',
                        { className: 'text-xs sm:text-sm text-[#334155] leading-relaxed' },
                        'Permite construir y controlar circuitos electrónicos reales que leen información del entorno mediante sensores y ejecutan acciones físicas con motores, servomotores y luces.'
                      )
                    )
                  : null,
                arduinoTab === 'learn'
                  ? el(
                      'div',
                      {
                        style: { backgroundColor: ARDUINO_THEME.cardTintBg },
                        className: 'rounded-2xl p-4 border border-white space-y-2.5'
                      },
                      el(
                        'h4',
                        { style: { color: ARDUINO_THEME.labelColor }, className: 'font-extrabold text-base' },
                        '¿Qué aprendes con Arduino?'
                      ),
                      el(
                        'ul',
                        { className: 'space-y-2 text-xs sm:text-sm text-[#334155]' },
                        el(
                          'li',
                          { className: 'flex items-start gap-2' },
                          el(Zap, { className: 'w-4 h-4 text-[#F43F5E] shrink-0 mt-0.5' }),
                          el(
                            'span',
                            null,
                            el('strong', null, 'Electrónica real:'),
                            ' montaje en protoboard, resistencias, voltaje y señales digitales/analógicas.'
                          )
                        ),
                        el(
                          'li',
                          { className: 'flex items-start gap-2' },
                          el(Zap, { className: 'w-4 h-4 text-[#F43F5E] shrink-0 mt-0.5' }),
                          el(
                            'span',
                            null,
                            el('strong', null, 'Programación en C++ y sistemas autónomos:'),
                            ' lectura de sensores ultrasónicos HC-SR04 y prototipos mecatrónicos desde cero.'
                          )
                        )
                      )
                    )
                  : null
              )
            )
          )
        )
      ),

      // -----------------------------------------------------------------------
      // 3. VENTANA POP-UP FINAL: 'QR_Movil_Sync.exe' (CÓDIGO QR ESCANEABLE)
      // -----------------------------------------------------------------------
      el(
        'section',
        { id: 'acceso-qr', className: 'scroll-mt-24' },
        el(
          AeroWindow,
          {
            id: 'qr',
            exeName: 'QR_Movil_Sync.exe',
            subtitle: 'Sincronización Celular Instantánea',
            icon: QrCode,
            statusText: 'Motor QR: Reed-Solomon GF(256) Pure JS | Escaneo Móvil: Listo',
            isMinimized: !!minimizedMap.qr,
            isClosed: !!closedMap.qr,
            onMinimize: () => toggleMinimize('qr'),
            onMaximize: () => setMaximizedWindowId('qr'),
            onClose: () => closeWindow('qr')
          },
          el(
            'div',
            { className: 'grid grid-cols-1 lg:grid-cols-12 gap-8 items-center' },
            // Columna de controles
            el(
              'div',
              { className: 'lg:col-span-7 space-y-5' },
              el(
                'div',
                {
                  className:
                    'inline-flex items-center gap-2 px-4 py-1.5 rounded-full bg-white/95 border border-[#38BDF8]/50 text-xs font-extrabold text-[#0078D7] shadow-sm'
                },
                el(QrCode, { className: 'w-4 h-4 text-[#00B4FF]' }),
                el('span', null, 'Acceso Móvil Directo')
              ),
              el(
                'h2',
                { className: 'text-3xl sm:text-4xl frutiger-aero-heading tracking-tight' },
                'Escanea y abre TECH MASTERS en tu celular'
              ),
              el(
                'p',
                { className: 'text-sm sm:text-base text-[#334155] leading-relaxed' },
                'Apunta la cámara de tu teléfono inteligente hacia este código QR para abrir esta página web directamente en tu celular. El código se genera en tiempo real mediante nuestro motor Reed-Solomon en JavaScript puro.'
              ),
              el(
                'div',
                { className: 'aero-metal-surface rounded-2xl p-4 sm:p-5 space-y-3' },
                el(
                  'label',
                  {
                    htmlFor: 'qr-url-input',
                    className: 'block text-xs font-extrabold uppercase tracking-wider text-[#0052A3]'
                  },
                  'Enlace codificado en el QR (Editable en tiempo real):'
                ),
                el(
                  'div',
                  { className: 'flex flex-col sm:flex-row gap-2.5' },
                  el(
                    'div',
                    { className: 'relative flex-1' },
                    el(Globe, {
                      className: 'w-4 h-4 text-[#00B4FF] absolute left-3.5 top-1/2 -translate-y-1/2'
                    }),
                    el('input', {
                      id: 'qr-url-input',
                      type: 'text',
                      value: qrUrl,
                      onChange: (ev) => setQrUrl(ev.target.value),
                      placeholder: 'https://...',
                      className:
                        'w-full pl-10 pr-4 py-2.5 rounded-xl bg-white border border-[#94A3B8] focus:border-[#00B4FF] focus:outline-none text-xs sm:text-sm font-semibold text-[#0F172A] shadow-inner'
                    })
                  ),
                  el(
                    'button',
                    {
                      type: 'button',
                      onClick: () => setQrUrl(defaultUrl),
                      className:
                        'px-4 py-2.5 rounded-xl bg-white border border-[#94A3B8] hover:border-[#00B4FF] text-xs font-extrabold text-[#334155] hover:text-[#0078D7] inline-flex items-center justify-center gap-1.5 transition-colors cursor-pointer shrink-0'
                    },
                    el(RotateCcw, { className: 'w-3.5 h-3.5' }),
                    el('span', null, 'URL Actual')
                  )
                ),
                el(
                  'div',
                  { className: 'flex flex-wrap items-center justify-between gap-3 pt-1' },
                  el(
                    'span',
                    { className: 'inline-flex items-center gap-1.5 text-xs text-[#475569] font-bold' },
                    el(Wifi, { className: 'w-3.5 h-3.5 text-[#00B4FF]' }),
                    'Listo para cámaras Android e iOS'
                  ),
                  el(
                    'button',
                    {
                      type: 'button',
                      onClick: handleDownloadQR,
                      className:
                        'aero-btn-primary px-4 py-2 rounded-xl text-white text-xs font-extrabold inline-flex items-center gap-1.5 cursor-pointer'
                    },
                    el(Download, { className: 'w-3.5 h-3.5' }),
                    el('span', null, 'Descargar QR (PNG)')
                  )
                )
              )
            ),
            // Pedestal cristalino con Canvas QR
            el(
              'div',
              { className: 'lg:col-span-5 flex flex-col items-center justify-center' },
              el(
                'div',
                {
                  className:
                    'relative p-6 rounded-3xl bg-gradient-to-b from-white via-[#F8FAFC] to-[#E0F2FE] border-2 border-white shadow-[0_20px_50px_rgba(0,120,215,0.22)]'
                },
                el('div', {
                  className: 'absolute top-3 left-3 w-6 h-6 border-t-4 border-l-4 border-[#00B4FF] rounded-tl-xl'
                }),
                el('div', {
                  className: 'absolute top-3 right-3 w-6 h-6 border-t-4 border-r-4 border-[#00B4FF] rounded-tr-xl'
                }),
                el('div', {
                  className: 'absolute bottom-3 left-3 w-6 h-6 border-b-4 border-l-4 border-[#00B4FF] rounded-bl-xl'
                }),
                el('div', {
                  className: 'absolute bottom-3 right-3 w-6 h-6 border-b-4 border-r-4 border-[#00B4FF] rounded-br-xl'
                }),
                el(
                  'div',
                  { className: 'bg-white p-3 rounded-2xl shadow-inner border border-[#CBD5E1]' },
                  el('canvas', {
                    ref: qrCanvasRef,
                    className: 'w-52 h-52 sm:w-60 sm:h-60 block mx-auto',
                    'aria-label': 'Código QR escaneable para abrir TECH MASTERS en celular'
                  })
                ),
                el(
                  'div',
                  { className: 'mt-4 text-center' },
                  el(
                    'span',
                    {
                      className:
                        'inline-flex items-center gap-1.5 px-4 py-1 rounded-full bg-gradient-to-r from-[#0078D7] to-[#00B4FF] text-white text-xs font-extrabold shadow-sm'
                    },
                    el(QrCode, { className: 'w-3.5 h-3.5' }),
                    'TECH MASTERS MOBILE PASS'
                  )
                )
              )
            )
          )
        )
      )
    ),

    // =========================================================================
    // MENÚ INICIO FLOTANTE ESTILO WINDOWS VISTA / 7 AERO
    // =========================================================================
    startMenuOpen
      ? el(
          'div',
          {
            className:
              'fixed bottom-20 left-3 sm:left-6 z-50 w-80 sm:w-96 win-aero-window rounded-2xl overflow-hidden shadow-2xl'
          },
          el(
            'div',
            { className: 'win-aero-titlebar px-4 py-3 flex items-center justify-between border-b border-white' },
            el(
              'div',
              { className: 'flex items-center gap-2.5' },
              el(
                'div',
                {
                  className:
                    'w-9 h-9 rounded-xl aero-btn-primary flex items-center justify-center text-white font-black'
                },
                el(Bot, { className: 'w-5 h-5' })
              ),
              el(
                'div',
                null,
                el('span', { className: 'block text-sm font-black text-[#0F172A]' }, 'TECH MASTERS OS'),
                el('span', { className: 'block text-[11px] font-bold text-[#0052A3]' }, 'Lanzador de Ventanas Aero')
              )
            ),
            el(
              'button',
              {
                type: 'button',
                onClick: () => setStartMenuOpen(false),
                className:
                  'win-caption-btn win-caption-close w-7 h-6 rounded-md flex items-center justify-center text-white text-xs font-black cursor-pointer'
              },
              '✕'
            )
          ),
          el(
            'div',
            { className: 'p-3 bg-white/95 space-y-1.5 max-h-72 overflow-y-auto' },
            WINDOW_CATALOG.map((win) => {
              const isClosed = !!closedMap[win.id];
              const isMin = !!minimizedMap[win.id];
              return el(
                'button',
                {
                  key: win.id,
                  type: 'button',
                  onClick: () => restoreAndFocusWindow(win.id, win.sectionId),
                  className:
                    'w-full px-3 py-2 rounded-xl hover:bg-[#E0F2FE] flex items-center justify-between text-left transition-colors cursor-pointer'
                },
                el(
                  'div',
                  { className: 'flex items-center gap-2.5' },
                  el(AppWindow, { className: 'w-4 h-4 text-[#0078D7]' }),
                  el('span', { className: 'text-xs font-extrabold text-[#0F172A]' }, win.exeName)
                ),
                el(
                  'span',
                  {
                    className: `text-[10px] font-bold px-2 py-0.5 rounded-full ${
                      isClosed
                        ? 'bg-rose-100 text-rose-700'
                        : isMin
                        ? 'bg-amber-100 text-amber-800'
                        : 'bg-sky-100 text-[#0078D7]'
                    }`
                  },
                  isClosed ? 'Cerrada (Abrir)' : isMin ? 'Minimizada' : 'Activa'
                )
              );
            })
          ),
          el(
            'div',
            { className: 'win-aero-statusbar px-3.5 py-2 flex items-center justify-between' },
            el(
              'button',
              {
                type: 'button',
                onClick: restoreAllWindows,
                className:
                  'aero-btn-primary px-3 py-1.5 rounded-lg text-white text-xs font-extrabold inline-flex items-center gap-1.5 cursor-pointer'
              },
              el(RotateCcw, { className: 'w-3.5 h-3.5' }),
              el('span', null, 'Restaurar Todas')
            ),
            el(
              'span',
              { className: 'inline-flex items-center gap-1 text-[11px] font-bold text-[#334155]' },
              el(Power, { className: 'w-3.5 h-3.5 text-[#0078D7]' }),
              'Aero Glass'
            )
          )
        )
      : null,

    // =========================================================================
    // BARRA DE TAREAS FLOTANTE ESTILO WINDOWS AERO CON BOTÓN ORBITAL 'TM'
    // =========================================================================
    el(
      'footer',
      { className: 'fixed bottom-2.5 inset-x-2.5 sm:inset-x-6 max-w-7xl mx-auto z-40' },
      el(
        'div',
        {
          className:
            'win-aero-taskbar rounded-2xl px-3 py-1.5 flex items-center justify-between gap-2.5'
        },
        // Botón de Inicio Orbital Brillante ('TM')
        el(
          'button',
          {
            type: 'button',
            onClick: () => setStartMenuOpen((prev) => !prev),
            title: 'Menú Inicio TECH MASTERS Aero',
            'aria-label': 'Inicio TECH MASTERS',
            className:
              'win-start-orb w-11 h-11 rounded-full flex items-center justify-center shrink-0 cursor-pointer relative overflow-hidden'
          },
          el('div', {
            className:
              'absolute top-0.5 inset-x-1.5 h-4 rounded-full bg-white/60 pointer-events-none'
          }),
          el(
            'span',
            {
              className:
                'relative z-10 text-white font-black text-sm tracking-tighter drop-shadow-[0_1px_2px_rgba(0,0,0,0.65)]'
            },
            'TM'
          )
        ),
        // Accesos rápidos a las ventanas en la barra de tareas
        el(
          'div',
          { className: 'flex-1 flex items-center gap-1.5 overflow-x-auto py-1' },
          WINDOW_CATALOG.map((win) => {
            const isClosed = !!closedMap[win.id];
            const isMin = !!minimizedMap[win.id];
            return el(
              'button',
              {
                key: win.id,
                type: 'button',
                onClick: () => restoreAndFocusWindow(win.id, win.sectionId),
                title: isClosed
                  ? `Reabrir ${win.exeName}`
                  : isMin
                  ? `Restaurar ${win.exeName}`
                  : `Ir a ${win.exeName}`,
                className: `px-2.5 py-1.5 rounded-xl text-[11px] font-extrabold whitespace-nowrap transition-all cursor-pointer flex items-center gap-1.5 border ${
                  isClosed
                    ? 'bg-white/10 text-slate-300 border-dashed border-white/30 hover:bg-white/25 hover:text-white'
                    : isMin
                    ? 'bg-white/20 text-sky-100 border-white/40 hover:bg-white/35'
                    : 'bg-gradient-to-b from-white/90 to-[#BAE6FD]/85 text-[#0F172A] border-white shadow-sm'
                }`
              },
              el('span', {
                style: !isClosed && !isMin ? { backgroundColor: win.dotColor } : undefined,
                className: `w-2 h-2 rounded-full ${
                  isClosed ? 'bg-slate-400' : isMin ? 'bg-amber-300' : 'bg-[#0078D7]'
                }`
              }),
              el('span', null, win.label)
            );
          })
        ),
        // Bandeja del sistema Windows Aero (System Tray)
        el(
          'div',
          {
            className:
              'hidden sm:flex items-center gap-2.5 px-3 py-1.5 rounded-xl bg-white/15 border border-white/25 text-white text-xs font-bold shrink-0'
          },
          el(ShieldCheck, { className: 'w-4 h-4 text-[#38BDF8]' }),
          el('span', { className: 'text-[11px] text-sky-100' }, 'Aero OS'),
          el('span', { className: 'font-mono text-xs text-white' }, clockText || '12:00')
        )
      )
    ),

    // =========================================================================
    // MODAL DE VENTANA MAXIMIZADA DE WINDOWS AERO
    // =========================================================================
    renderMaximizedModal()
  );
}