(defproject latte "0.3.3-SNAPSHOT"
  :description "LaTTe : a Laboratory for Type Theory Experiments"
  :url "https://github.com/fredokun/LaTTe.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [clj-by-example "0.1.0"]]
  :codox {:metadata {:doc/format :markdown}
          :namespaces [latte.core latte.prop latte.classic
                       latte.quant latte.equal latte.rel]}
  :plugins [[lein-codox "0.9.5"]])

