;;; Copyright (c) 2000-2013 Andrew W. Keep, R. Kent Dybvig
;;; See the accompanying file Copyright for detatils

(library (tests unit-test-helpers-implementation)
  (export with-output-to-string display-condition)
  (import (only (chezscheme) with-output-to-string display-condition)))
