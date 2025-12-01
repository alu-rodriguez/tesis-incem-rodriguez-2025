# tesis-incem-rodriguez-2025

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

