;;; tll-mode.el --- major mode for tll -*- lexical-binding: t; -*-
(setq tll-keywords '("of" "size"))
(setq tll-lambda '("fn" "ln" "fun" "function" "val" "main" "where"))
(setq tll-builtin '("let" "let*" "in" "rew" "match" "as" "with" "end"
                    "if" "then" "else" "fork" "return"
                    "open" "send" "recv" "close"))

(setq tll-pragma-start-regexp "\\(?:#\\)")
(setq tll-pragma-regexp "\\(?:program\\|logical\\|multiplicative\\|additive\\)")
(setq tll-sorts-regexp "\\(?:\\_<U\\_>\\|\\_<L\\_>\\)")
(setq tll-keywords-regexp (regexp-opt tll-keywords 'symbols))
(setq tll-lambda-regexp (regexp-opt tll-lambda 'symbols))
(setq tll-builtin-regexp (regexp-opt tll-builtin 'symbols))
(setq tll-quantifier-regexp "\\(?:∀\\|forall\\|∃\\|exists\\|⇑\\|⇓\\|•\\)")
(setq tll-magic-regexp "\\(?:#magic\\)")
(setq tll-absurd-regexp "\\(?:!!\\)")
(setq tll-infer-regexp "\\(?:infer_tm\\)")
(setq tll-check-regexp "\\(?:check_tm\\)")
(setq tll-assert-regexp "\\(?:assert_equal\\)")

(setq tll-font-lock-keywords
      `(("\\(\\<inductive\\>\\|\\<def\\>\\)\s*\\([[:graph:]]*\\)"
         (1 font-lock-keyword-face)
         (2 font-lock-variable-name-face))
        (,tll-magic-regexp . font-lock-warning-face)
        (,tll-absurd-regexp . font-lock-warning-face)
        (,tll-pragma-start-regexp . font-lock-keyword-face)
        (,tll-pragma-regexp . font-lock-keyword-face)
        (,tll-sorts-regexp . font-lock-constant-face)
        (,tll-keywords-regexp . font-lock-keyword-face)
        (,tll-lambda-regexp . font-lock-keyword-face)
        (,tll-builtin-regexp . font-lock-builtin-face)
        (,tll-quantifier-regexp . font-lock-constant-face)
        (,tll-infer-regexp . font-lock-string-face)
        (,tll-check-regexp . font-lock-warning-face)
        (,tll-assert-regexp . font-lock-doc-face)
        ))

(defvar tll-mode-syntax-table nil "syntax table for tll-mode")
(setq tll-mode-syntax-table
      (let ((st (make-syntax-table)))
        ;; comments
        (modify-syntax-entry ?/ ". 14nb" st)
        (modify-syntax-entry ?- ". 123" st)
        (modify-syntax-entry ?\n ">" st)

        ;; strings
        (modify-syntax-entry ?\" "\"" st)
        (modify-syntax-entry ?\' "\"" st)

        (modify-syntax-entry ?< "." st)
        (modify-syntax-entry ?> "." st)
        st))

(add-hook 'tll-mode-hook
          (lambda ()
            (setq prettify-symbols-alist
                  '(("->" . ?→)
                    ("<-" . ?←)
                    ("=>" . ?⇒)
                    ("-o" . ?⊸)
                    (":=" . ?≔)
                    ("exists" . ?∃)
                    ("forall" . ?∀)))
            (prettify-symbols-mode 1)))

;;;###autoload
(define-derived-mode tll-mode prog-mode
  "TLL"
  "Major mode for editing TLL"
  (setq font-lock-defaults '((tll-font-lock-keywords)))
  (set-syntax-table tll-mode-syntax-table)
  (setq-local comment-start "--")
  (setq-local comment-start-skip "--+[\t ]*")
  (setq-local comment-end ""))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tll" . tll-mode))
(provide 'tll-mode)
