# Unification in Agda

This is a tutorial on how Agda infers things.

## How to read

There are two ways to read the tutorial:

1. [click this link](https://htmlpreview.github.io/?https://github.com/effectfully/unification-in-agda/blob/master/UnificationInAgda.html) to read the rendered HTML. Simple and sufficient, if you only want to read and not play with the code or contribute
2. if you do want to play with the code, then install Agda, clone the repo, open the `UnificationInAgda.lagda.md` file, type check it and only then read

**IMPORTANT**: reading `UnificationInAgda.lagda.md` without type checking the file beforehand is a non-option as making Agda color the code is important for understanding how things get type checked. Hence reading `UnificationInAgda.lagda.md` directly on GitHub is a non-option as well as GitHub's syntax highlighting is insufficient and the file has to actually be type checked.

## Contributing

Building the HTML is a bit of a PITA as it requires several tools to be installed and several commands to be executed. So if you're going to create a PR, don't bother updating the HTML file, I'll do that myself.

### Building the HTML

#### Prerequisites

1. install [`agda`](https://github.com/agda/agda) and its [standard library](https://github.com/agda/agda-stdlib)
2. install [`htmlize`](https://github.com/hniksic/emacs-htmlize) for `emacs`. For example via `(use-package htmlize :ensure t)`
3. install [`agda-html-to-md`](https://github.com/effectfully/agda-html-to-md)
4. install [`pandoc`](https://pandoc.org/installing.html)
5. add this to your `.emacs.d` file:

```elisp
(global-set-key (kbd "C-x a h") 'htmlize-buffer)
(fset 'generate-unification-in-agda-html
  [?\C-x ?h ?\C-u ?\M-| ?a ?g ?d ?a ?- ?h ?t ?m ?l ?- ?t ?o ?- ?m ?d return ?\C-x ?h ?\M-| ?p ?a ?n ?d ?o ?c ?  ?- ?- ?t ?o ?c ?  ?- ?s ?  ?- ?o ?  ?U ?n ?i ?f ?i ?c ?a ?t ?i ?o ?n ?I ?n ?A ?g ?d ?a ?. ?h ?t ?m ?l return])
(global-set-key (kbd "C-x a u") 'generate-unification-in-agda-html)
```

#### Generating the HTML

**IMPORTANT**: wait for each command to finish.

1. open `UnificationInAgda.lagda.md` in emacs
2. `C-c C-l` (type check the file)
3. `C-x a h` (initial htmlization of the buffer)
4. `C-x a u` (generate the final `UnificationInAgda.html` file)
