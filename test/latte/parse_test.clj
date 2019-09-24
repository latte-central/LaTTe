
(ns latte.parse-test
  (:require [latte.parse :as sut :refer [parse-definition]]
            [clojure.test :as t :refer [deftest testing is]]))

(deftest parse-definition-test

  (testing "parse-definition"
    
    (is (= (parse-definition ['dname "dummy def" '[T :type]])
           '[:ko "Definition form (with docstring) requires at least 4 arguments."
             {:def-name dname, :nb-args 3}]))

    (is (= (parse-definition [42 "dummy def" '[T :type] '(==> T :type)])
           '[:ko "Definition name must be a symbol." {:name 42}]))


    (is (= (parse-definition ['dname "dummy def" '[T :type] '(==> T :type)])
           '[:ok "" {:def-name dname, :def-doc "dummy def", :params [[T :type]], :body (==> T :type)}]))

    (is (= (parse-definition ['dname "dummy def" '[T :type] '(==> T :type) :garbage])
           '[:ko "Too many arguments for definition." {:def-name dname, :nb-args 5, :garbage (:garbage)}]))

    (is (= (parse-definition ['dname "dummy def" '[[T :type]] '(==> T :type)])
           '[:ok "" {:def-name dname, :def-doc "dummy def", :params [[T :type]], :body (==> T :type)}]))
    
    (is (= (parse-definition ['dname "dummy def" '[T :type, U :type] '(==> T U :type)])
           '[:ok "" {:def-name dname, :def-doc "dummy def", :params [[T :type] [U :type]], :body (==> T U :type)}]))
    
    (is (= (parse-definition ['dname "dummy def" '[T :type, (set T) :type] '(==> T U :type)])
           '[:ko "Cannot parse parameter list" {:def-params dname,
                                                :cause ["Expecting a parameter name as a symbol." {:param (set T)}]}]))
    
    (is (= (parse-definition ['dname "dummy def" '[[T :type]  [U :type]] '(==> T U :type)])
           '[:ok "" {:def-name dname, :def-doc "dummy def", :params [[T :type] [U :type]], :body (==> T U :type)}]))

    (is (= (parse-definition ['dname "dummy def" '[[T :type]  [U :type 42]] '(==> T U :type)])
           '[:ko "Cannot parse parameter list" {:def-params dname,
                                                :cause ["Parameter must be a pair `[name type]`."
                                                        {:param [U :type 42]}]}]))
    
    ))


   



