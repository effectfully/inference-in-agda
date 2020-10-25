# Unification in Agda

## Building the HTML

### Prerequisites

1. install [`htmlize`](https://github.com/hniksic/emacs-htmlize) for `emacs`. For example via

```elisp
(use-package htmlize
  :ensure t)
```

2. globally install [`agda-html-to-md`](https://github.com/effectfully/agda-html-to-md)

3. globally install [`pandoc`](https://pandoc.org/installing.html)

4. add this to your `.emacs.d` file:

```
(global-set-key (kbd "C-x a h") 'htmlize-buffer)
(fset 'generate-unification-in-agda-html
  [?\C-x ?h ?\C-u ?\M-| ?a ?g ?d ?a ?- ?h ?t ?m ?l ?- ?t ?o ?- ?m ?d return ?\C-x ?h ?\M-| ?p ?a ?n ?d ?o ?c ?  ?- ?- ?t ?o ?c ?  ?- ?s ?  ?- ?o ?  ?U ?n ?i ?f ?i ?c ?a ?t ?i ?o ?n ?I ?n ?A ?g ?d ?a ?. ?h ?t ?m ?l return])
(global-set-key (kbd "C-x a u") 'generate-unification-in-agda-html)
```

### Generating the HTML

*IMPORTANT*: wait for each command to finish.

1. open `UnificationInAgda.lagda.md` in emacs
2. `C-c C-l` (type check the file)
3. `C-x a h` (initial htmlization of the buffer)
4. `C-x a u` (generate the final `UnificationInAgda.html` file)
