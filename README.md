# tesis-incem-rodriguez-2025

## 🌐 Spanish Overview (ES) / Descripción en Español

Tesis de licenciatura de **Matías Nicolás Incem** y **Alejandra Alicia Rodríguez**  
Departamento de Computación – FCEyN, Universidad de Buenos Aires (UBA), 2025.

Este repositorio contiene los modelos Alloy, las ejecuciones experimentales y el documento final de la tesis titulada:

> **Modal Abstractions for Smart-Contract Verification: Reproducción, Extensión y Análisis Experimental**

El trabajo se centra en reproducir los experimentos del paper original de **Godoy et al.** y extenderlos con nuevos casos de estudio creados específicamente para esta tesis.

---

# Contenidos del repositorio

```text
.
├── casos_de_estudio/
├── output_reproducciones/
├── tesis.pdf
├── THESIS_LICENSE.md
└── LICENSE
```


## 📂 `casos_de_estudio/` — *Casos nuevos creados por esta tesis*

Este directorio contiene **variantes con issues de los casos de estudio originales desarrollados por los autores** para evaluar el comportamiento de Alloy4PA y de las abstracciones modal/predicate en **escenarios no cubiertos por el paper original**.

Incluye:

- Modelos Alloy4PA completos.
- Variantes con **bugs de negocio** diseñados para inducir degradaciones `must → may`, estados trabados o comportamientos no deseados.
- Configuraciones que permiten analizar:
  - Robustez de la lógica de negocio.
  - Sensibilidad del enfoque a cambios paramétricos.
  - Capacidad para revelar errores que las abstracciones “may-only” no pueden detectar.

> **Este es el corazón del aporte original de la tesis.**

---

## 📂 `reproducciones/` — *Reproducción de los benchmarks del paper original*

En este directorio se encuentran las **corridas realizadas por los autores para replicar todos los resultados de los benchmarks del trabajo de Godoy et al.** (SimpleMarket, AssetTransfer, RockPaperScissors, etc.).

Su objetivo es **verificar que los resultados obtenidos con Alloy4PA coinciden con los informados por los autores originales**.

Contiene:

- Salidas completas de Alloy4PA.
- Tiempos de cómputo para EPA, BEPA, SBEPA.
- Tamaños de los grafos may/must.
- Logs y estadísticas de consultas.

> Estos resultados actúan como **baseline validado** para luego poder comparar los nuevos casos creados en esta tesis.

---

## 📄 `tesis.pdf`

Versión final y completa de la tesis, incluyendo:

- Introducción y motivación.
- Marco teórico (predicate abstraction, modal abstractions, Alloy4PA, etc.).
- Reproducción de experimentos originales.
- Diseño de nuevos casos con bugs intencionales.
- Resultados, comparaciones y análisis cualitativo/cuantitativo.

---

## 📄 `THESIS_LICENSE.md`

Licencia específica aplicada al PDF de la tesis.  
Únicamente regula el uso, distribución y citación del documento.

---

## 📄 `LICENSE` (MIT)

Licencia MIT para el **código, modelos Alloy y scripts auxiliares** del repositorio.  
No aplica al PDF.

---

## 👥 Autores

- **Matías Nicolás Incem** – Co-autor de la tesis y de los modelos experimentales.  
- **Alejandra Alicia Rodríguez** – Co-autora de la tesis y de los modelos experimentales.

---

## 📚 Citación

Si utilizás este repositorio o parte de sus modelos, por favor citá la tesis según el formato de tu disciplina (APA, IEEE, ACM, etc.).  
Los datos bibliográficos completos se encuentran en la carátula de `tesis.pdf`.

---

## 🌐 English Overview (EN) / Descripción en Inglés

This repository contains the models, experimental artifacts, and final PDF for the undergraduate thesis *“Modal Abstractions for Smart-Contract Verification”* (written in **Spanish**) by **Matías Nicolás Incem** and **Alejandra Alicia Rodríguez**, Department of Computer Science, University of Buenos Aires (UBA), 2025.

The thesis work includes:

- A **reproduction** of the original benchmarks from Godoy et al. (SimpleMarket, AssetTransfer, RockPaperScissors, etc.) to validate Alloy4PA’s behavior against previously published results.
- The design and execution of **new case studies**, created specifically for this thesis, to evaluate modal abstractions in additional scenarios involving business-logic flaws and parameter variations.

### Repository structure (English summary)

- **`casos_de_estudio/`**  
  Contains the *new case studies* created by the authors. These include Alloy4PA models and buggy contract variants used to analyze must→may degradations, stuck states, and semantic robustness.

- **`reproducciones/`**  
  Contains the *replications of the original benchmarks*. These are the authors’ runs of the Alloy4PA experiments as described in Godoy et al., including performance data, logs, and generated may/must graphs.

- **`tesis.pdf`**  
  The full thesis document (*written in Spanish*).

- **`LICENSE`**  
  MIT License for the models and code.

- **`THESIS_LICENSE.md`**  
  Specific license terms for the thesis PDF.

### Authors

- **Matías Nicolás Incem** – Co-author of the thesis and experimental models.  
- **Alejandra Alicia Rodríguez** – Co-author of the thesis and experimental models.

### Citation

If you use this repository or any of its models, please cite the thesis in your preferred academic style (APA, IEEE, ACM, etc.).  
Bibliographic information is available in the cover page of `tesis.pdf`.
