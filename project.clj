(defproject latte "0.99.4-SNAPSHOT"
  :description "LaTTe : a Laboratory for Type Theory Experiments"
  :url "https://github.com/fredokun/LaTTe.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.9.0-beta1"]
                 [org.clojure/core.match "0.3.0-alpha5"]
                 [latte-kernel "0.99.4-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte.core latte.prop latte.classic
                       latte.quant latte.equal latte.rel latte.fun]}
  :plugins [[lein-codox "0.10.3"]])

