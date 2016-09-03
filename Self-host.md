This is how one can check with planck if the code is self-host friendly.

(Full explanations about managing dependencies in planck are [here](http://planck-repl.org/dependencies.html).)

```bash
git clone git@github.com:viebel/clj-by-example.git # get a version of clj-by-example that does nothing
brew install planck (version should be >= 1.16)
planck -c`lein classpath`
cljs.user=> (ns my-fixed-points.complete-lattices (:refer-clojure :exclude [and or not set]) (:require-macros [latt
e.core :as latte :refer [definition defthm defaxiom assume have proof try-proof]]) (:require [latte.rel :as rel :re
fer [rel]]))
```
