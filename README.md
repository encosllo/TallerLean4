# Taller de Lean 4

Repositori del Taller de Lean 4 impartit a la Facultat de Ciències
Matemàtiques de la Universitat de València.

## Com treballar amb aquest repositori

Per a treballar amb aquest repositori recomanem utilitzar l'editor
[Visual Studio Code](https://code.visualstudio.com) amb les extensions
recomanades per a Lean 4:
- [lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
- [Paperproof](https://marketplace.visualstudio.com/items?itemName=paperproof.paperproof)

Aquestes i altres extensions estan incloses en el fitxer de recomanacions
d'extensions de Visual Studio Code que es pot trobar a la carpeta
`.vscode` d'aquest repositori.

La instal·lació de Lean 4 es pot fer automaticament amb la propia extensió
de Lean 4, però també es pot fer manualment seguint les instruccions de la
[web de Lean 4](https://leanprover.github.io/lean4/doc/setup.html).

Podeu trobar altres requirements i detalls al [blog del Taller de Lean
4](https://www.uv.es/coslloen/Lean4.html).

### Inicialització

Clonem el repositori
```bash
git clone https://github.com/encosllo/TallerLean4
```

Recordeu obrir la carpeta on esteu treballant al Visual Studio Code.

Per tal d'activar l'entorn de treball, només cal executar la següent comanda
en la terminal:

```bash
lake build # <- Per compilar el nostre i codi i poder accedir a ell
```

Si treballeu amb Visual Studio Code, és possible que aparega un _pop-up_
que indica que és necessari fer un _rebuild_ de les dependències. Feu click
al botó de _Rebuild_ per a fer-ho.

### Flux de treball

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

Ara ja podeu treballar a la branca local i fer els vostres commits,
preferiblement en fitxers diferents als que ja estan en el repositori per
tal de no tindre conflictes amb actualitzacions futures.

Quan vulgueu actualitzar el vostre repositori amb les actualitzacions
del repositori remot, podeu fer un _rebase_ de la branca remota `main`:

```bash
git rebase origin/main
```
