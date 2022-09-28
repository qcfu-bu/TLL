;;; tll-mode.el --- major mode for tll -*- lexical-binding: t; -*-

(setq tll-keywords '("def" "theorem" "axiom" "param" "inductive" "where"))
(setq tll-types '("U" "L" "let" "in" "match" "as" "return" "with"))

(setq tll-keywords-regexp (regexp-opt tll-keywords 'words))
(setq tll-forall-regexp "\\(?:\\_<forall\\_>\\|∀\\)")
(setq tll-lambda-regexp "\\(?:\\_<fun\\_>\\|λ\\)")
(setq tll-fixpoint-regexp "\\(?:\\_<fix\\_>\\|μ\\)")
(setq tll-type-regexp (regexp-opt tll-types 'words))

(setq tll-font-lock-keywords
      `((,tll-type-regexp . font-lock-type-face)
        (,tll-keywords-regexp . font-lock-keyword-face)
        (,tll-forall-regexp . font-lock-type-face)
        (,tll-lambda-regexp . font-lock-type-face)
        (,tll-fixpoint-regexp . font-lock-type-face)))

;;;###autoload
(define-derived-mode tll-mode prog-mode
  "tll mode"
  "Major mode for editing TLL"
  (setq font-lock-defaults '((tll-font-lock-keywords)))
  (setq-local comment-start "--")
  (setq-local comment-start-skip "--+[\t ]*")
  (setq-local comment-end "")
  (font-lock-add-keywords nil '(("--.+" . font-lock-comment-face)))
  (company-mode 1)
  (add-to-list 'company-backends 'company-math-symbols-unicode))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tll" . tll-mode))
(provide 'tll-mode)
