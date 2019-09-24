
(ns latte.parse-test
  (:require [latte.parse :as sut :refer [parse-definition]]
            [clojure.test :as t :refer [deftest testing is]]))

(deftest parse-definition-test

  (testing "parse-definition"
    
    (is (= (parse-definition :definition ['dname "dummy def" '[T :type]])
           '[:ko "Definition form (with docstring) requires at least 4 arguments." {:def-name dname, :nb-args 3}]))

    (is (= (parse-definition :definition [42 "dummy def" '[T :type] '(==> T :type)])
           '[:ko "Definition name must be a symbol." {:name 42}]))


    (is (= (parse-definition :definition ['dname "dummy def" '[T :type] '(==> T :type)])
           '[:ok "" {:def-name dname, :doc "dummy def", :params [[T :type]], :body (==> T :type)}]))

    (is (= (parse-definition :definition ['dname "dummy def" '[T :type] '(==> T :type) :garbage])
           '[:ko "Too many arguments for definition." {:def-name dname, :nb-args 5, :garbage (:garbage)}]))

    (is (= (parse-definition :definition ['dname "dummy def" '[[T :type]] '(==> T :type)])
           '[:ok "" {:def-name dname, :doc "dummy def", :params [[T :type]], :body (==> T :type)}]))
    
    (is (= (parse-definition :definition ['dname "dummy def" '[T :type, U :type] '(==> T U :type)])
           '[:ok "" {:def-name dname, :doc "dummy def", :params [[T :type] [U :type]], :body (==> T U :type)}]))
    
    (is (= (parse-definition :definition ['dname "dummy def" '[T :type, (set T) :type] '(==> T U :type)])
           '[:ko "Cannot parse parameter list" {:def-name dname, :from {:param (set T), :msg "Expecting a parameter name as a symbol."}}]))
    
    (is (= (parse-definition :definition ['dname "dummy def" '[[T :type]  [U :type]] '(==> T U :type)])
           '[:ok "" {:def-name dname, :doc "dummy def", :params [[T :type] [U :type]], :body (==> T U :type)}]))

    (is (= (parse-definition :definition ['dname "dummy def" '[[T :type]  [U :type 42]] '(==> T U :type)])
           '[:ko "Cannot parse parameter list" {:def-name dname, :from {:param [U :type 42], :msg "Parameter must be a pair `[name type]`."}}]))
    
    (is (= (parse-definition :definition ['dname "dummy def" '[[T :type]  [U :type] V] '(==> T U :type)])
           '[:ko "Cannot parse parameter list" {:def-name dname, :from {:param-name V, :msg "Parameter is without a type."}}]))

    ))


   



