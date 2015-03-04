(defproject latte "0.0.1"
  :description "LaTTe : a Laboratory for Type Theory experiments"
  :url "https://github.com/fredokun/LaTTe.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.6.0"]]
  :plugins [[cider/cider-nrepl "0.8.2"]]
  :main ^:skip-aot latte.core
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all}})

