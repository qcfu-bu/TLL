;;; tll-mode.el --- major mode for tll -*- lexical-binding: t; -*-

(setq tll-keywords '("def"
                     "theorem"
                     "axiom"
                     "param"
                     "inductive"
                     "where"))
(setq tll-types '("U"
                  "L"
                  "forall"
                  "fun"
                  "fix"
                  "let"
                  "in"
                  "match"
                  "as"
                  "return"
                  "with"))

(setq tll-keywords-regexp (regexp-opt tll-keywords 'words))
(setq tll-type-regexp (regexp-opt tll-types 'words))

(setq tll-font-lock-keywords
      `((,tll-type-regexp . font-lock-type-face)
        (,tll-keywords-regexp . font-lock-keyword-face)))

;;;###autoload
(define-derived-mode tll-mode prog-mode
  "tll mode"
  "Major mode for editing TLL"
  (setq font-lock-defaults '((tll-font-lock-keywords)))
  (setq-local comment-start "--")
  (setq-local comment-start-skip "--+[\t ]*")
  (setq-local comment-end "")
  (font-lock-add-keywords nil '(("--.+" . font-lock-comment-face))))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tll" . tll-mode))

(setq tll-keywords nil)
(setq tll-types nil)
(setq tll-keywords-regexp nil)
(setq tll-type-regexp nil)
(provide 'tll-mode)
