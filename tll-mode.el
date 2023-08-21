;;; tll-mode.el --- major mode for tll -*- lexical-binding: t; -*-

;;;; font lock for syntax
(setq tll-start '("#" "\?" "!"))
(setq tll-pragma '("program" "logical" "hint"))
(setq tll-sorts '("U" "L" "Type"))
(setq tll-keywords '("of" "layout"))
(setq tll-lambda '("fn" "ln" "fun" "function" "val" "main" "where"))
(setq tll-builtin '("let" "let*" "in" "rew" "match" "as" "with" "end"
                    "if" "then" "else" "fork" "return"
                    "open" "send" "recv" "close"))
(setq tll-quantifier '("∀" "forall" "∃" "exists"))
(setq tll-highlights '("→" "->" "⊸" "-o" "≔" ":=" "⇒" "=>" ":"))
(setq tll-intense '("#magic" "!!") )

(setq tll-start-regexp (regexp-opt tll-start nil))
(setq tll-pragma-regexp (regexp-opt tll-pragma 'symbols))
(setq tll-sorts-regexp (regexp-opt tll-sorts 'symbols))
(setq tll-keywords-regexp (regexp-opt tll-keywords 'symbols))
(setq tll-lambda-regexp (regexp-opt tll-lambda 'symbols))
(setq tll-builtin-regexp (regexp-opt tll-builtin 'symbols))
(setq tll-quantifier-regexp (regexp-opt tll-quantifier nil))
(setq tll-highlights-regexp (regexp-opt tll-highlights nil))
(setq tll-intense-regexp (regexp-opt tll-intense nil))

;;;; font lock for log messages
(setq tll-log-group1 '("infer_tm"))
(setq tll-log-group2 '("check_tm"))
(setq tll-log-group3 '("assert_equal" "simpl_iprbm" "simpl_pprbm"))

(setq tll-log-group1-regexp (regexp-opt tll-log-group1 nil))
(setq tll-log-group2-regexp (regexp-opt tll-log-group2 nil))
(setq tll-log-group3-regexp (regexp-opt tll-log-group3 nil))


(setq tll-font-lock-keywords
      `(;; top level declarations
        ("\\(\\<inductive\\>\\|\\<def\\>\\|\\<extern\\>\\|\\<notation\\>\\)\s*\\([[:graph:]]*\\)"
         (1 font-lock-keyword-face)
         (2 font-lock-variable-name-face))
        ;; expression syntax
        (,tll-intense-regexp . font-lock-warning-face)
        (,tll-start-regexp . font-lock-keyword-face)
        (,tll-pragma-regexp . font-lock-keyword-face)
        (,tll-sorts-regexp . font-lock-constant-face)
        (,tll-keywords-regexp . font-lock-keyword-face)
        (,tll-lambda-regexp . font-lock-keyword-face)
        (,tll-builtin-regexp . font-lock-builtin-face)
        (,tll-quantifier-regexp . font-lock-constant-face)
        (,tll-highlights-regexp . font-lock-type-face)
        ;; log file messages
        (,tll-log-group1-regexp . font-lock-string-face)
        (,tll-log-group2-regexp . font-lock-warning-face)
        (,tll-log-group3-regexp . font-lock-doc-face)
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
