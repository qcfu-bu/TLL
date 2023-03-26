;;; tll-mode.el --- major mode for tll -*- lexical-binding: t; -*-
(setq tll-types '("let" "in" "rew" "match" "with" "end" "fork" "return"))
(setq tll-keywords '("of"))
(setq tll-session '("open" "send" "recv" "close"))

(setq tll-sorts-regexp "\\(?:\\_<U\\_>\\|\\_<L\\_>\\)")
(setq tll-types-regexp (regexp-opt tll-types 'words))
(setq tll-keywords-regexp (regexp-opt tll-keywords 'words))
(setq tll-session-regexp (regexp-opt tll-session 'words))
(setq tll-quantifier-regexp "\\(?:∀\\|∃\\|⇑\\|⇓\\|•\\)")
(setq tll-lambda-regexp "\\(?:\\_<fn\\_>\\|\\_<ln\\_>\\|\\_<fix\\_>\\)")

(setq tll-font-lock-keywords
      `(("\\(\\<inductive\\>\\|\\<program\\>\\|\\<logical\\>\\)\s*\\([[:graph:]]*\\)"
         (1 font-lock-keyword-face)
         (2 font-lock-variable-name-face))
        (,tll-sorts-regexp . font-lock-constant-face)
        (,tll-types-regexp . font-lock-type-face)
        (,tll-keywords-regexp . font-lock-keyword-face)
        (,tll-session-regexp . font-lock-builtin-face)
        (,tll-quantifier-regexp . font-lock-constant-face)
        (,tll-lambda-regexp . font-lock-keyword-face)))

(defvar tll-mode-syntax-table nil "syntax table for tll-mode")
(setq tll-mode-syntax-table
      (let ((st (make-syntax-table)))
        (modify-syntax-entry ?/ ". 14nb" st)
        (modify-syntax-entry ?- ". 123" st)
        (modify-syntax-entry ?\n ">" st)
        st))

;;;###autoload
(define-derived-mode tll-mode prog-mode
  "tll mode"
  "Major mode for editing TLL"
  (setq font-lock-defaults '((tll-font-lock-keywords)))
  (set-syntax-table tll-mode-syntax-table)
  (setq-local comment-start "--")
  (setq-local comment-start-skip "--+[\t ]*")
  (setq-local comment-end "")
  (company-mode 1)
  (add-to-list 'company-backends 'company-math-symbols-unicode))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tll" . tll-mode))
(provide 'tll-mode)
