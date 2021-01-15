(defproject latte "1.0b10-SNAPSHOT"
  :description "LaTTe : a Laboratory for Type Theory Experiments"
  :url "https://github.com/fredokun/LaTTe.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [org.clojure/core.match "0.3.0"]
                 [digest "1.4.9"]
                 [com.taoensso/timbre "4.10.0"]
                 [latte-kernel "1.0b10-SNAPSHOT"]]
  :codox {:output-path "docs"
          :metadata {:doc/format :markdown}
          :namespaces [latte.core]}
  :plugins [[lein-codox "0.10.7"]])





