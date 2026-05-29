(defproject latte "1.0"
  :description "LaTTe : The clojure-based Proof Assistant"
  :url "https://github.com/fredokun/LaTTe.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.12.145"]
                 [org.clojure/core.match "1.1.0"]
                 [org.clj-commons/digest "1.4.100"]
                 [com.taoensso/timbre "6.6.1"]
                 [latte-kernel "1.0"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte.core]}
  :plugins [[lein-codox "0.10.8"]])

