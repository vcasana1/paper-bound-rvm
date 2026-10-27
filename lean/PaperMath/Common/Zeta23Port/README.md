# Port de la desigualdad de Hilbert generalizada (Montgomery–Vaughan) desde zeta23

Origen: <https://github.com/anthropics/zeta-23-lean>, carpeta `zeta23/`, ficheros `Zeta23/MV.lean`, `Zeta23/MV/*.lean`, `Zeta23/LinAlg/PosIndex.lean`, `Zeta23/LinAlg/HermitianPosPart.lean` y la definición `MVHilbert` de `Zeta23/Hypotheses.lean`. Copyright (c) 2026 Anthropic, PBC; Apache License 2.0 (`LICENSE`, `NOTICE_zeta23`).

Modificaciones: rutas de módulo `Zeta23.*` → `PaperMath.Common.Zeta23Port.*`; `import Mathlib` sustituido por importaciones concretas; `Hypotheses.lean` reducido a la definición `MVHilbert`. Las demostraciones no se han modificado. Compila con Lean 4.36.0-rc1 y Mathlib v4.36.0-rc1, y `Zeta23.MV.mv_hilbert` depende solo de los axiomas estándar.
