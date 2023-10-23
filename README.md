# Taller de Lean 4

Repositori del Taller de Lean 4 impartit a la Facultat de Ciències
Matemàtiques de la Universitat de València.

## Com treballar amb aquest repositori

### Entorn de Lean i altres requeriments

Per tal d'activar l'entorn de treball, només cal executar el següent
comandament:

```bash
lake update
```

Podeu trobar altres requirements i detalls al [blog del Taller de Lean
4](https://www.uv.es/coslloen/Lean4.html).

### Workflow

Una idea per a treballar a les sessions amb el codi actualitzat del
repositori és, en primer lloc, clonar el repositori:

```bash
git clone https://github.com/encosllo/TallerLean4
```

A continuació, cal obrir un terminal a la carpeta del repositori i crear
una branca local nova amb el vostre nom:

```bash
git branch <nom> # <- Crear la branca
git switch <nom> # <- Canviar a la branca
```

Ara ja podeu treballar a la branca local i fer els vostres commits.
Quan comencem una nova sessió, actualitzarem el repositori fent un rebase:

```bash
git rebase origin/main
```
