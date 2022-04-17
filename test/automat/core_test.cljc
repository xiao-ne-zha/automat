(ns automat.core-test
  (:require
    [automat.core :as a ]
    [automat.fsm :as fsm]
    #?(:clj [clojure.test :refer :all]
       :cljs [cemerick.cljs.test])
    #?(:clj [criterium.core :as c]))
  #?(:cljs (:require-macros
             [cemerick.cljs.test :refer [deftest testing is are]])))

(defn accepts? [f fsm start-index stream-index s]
  (let [state (f fsm nil s)]
    (and
      (:accepted? state)
      (= start-index (:start-index state))
      (= stream-index (:stream-index state)))))

(def backends [:base #?(:clj :eval) :backtrack])

(deftest test-find
  (doseq [backend backends]
    (testing backend
      (are [fsm input-seqs]
        (let [fsm' (a/compile fsm {:backend backend})]
          (every?
            (fn [[start end s]]
              (accepts? a/find fsm' start end s))
            (partition 3 input-seqs)))

        a/any
        [0 1 [1]
         0 1 [2 3]
         0 1 [3 3 3]]

        [(list 1 2) (list 3)]
        [0 2 [[1 2] [3]]]

        (a/+ :a)
        [0 1 [:a :a]
         1 2 [:b :a :a]]

        (a/+ 1)
        [0 1 [1 1]
         1 2 [0 1 1]]

        [1 2 3]
        [0 3 [1 2 3]
         2 5 [1 1 1 2 3 2 1]]

        (a/or
          [1 2 3]
          [2 3])
        [0 3 [1 2 3]
         0 2 [2 3]
         1 3 [0 2 3]]))))

(deftest test-greedy-find
  (doseq [backend (remove #(= :backtrack %) backends)]
    (testing backend
      (are [fsm input-seqs]
          (let [fsm' (a/compile fsm {:backend backend})]
            (every?
             (fn [[start end s]]
               (accepts? a/greedy-find fsm' start end s))
             (partition 3 input-seqs)))

        a/any
        [0 1 [1]
         0 1 [2 3]]

        (a/+ 1)
        [0 2 [1 1]
         1 3 [0 1 1 0]]))))

(deftest test-backtrack-greedy-find
  (testing :backtrack
    (are [fsm input-seqs]
        (let [fsm' (a/compile fsm {:backend :backtrack})]
          (every?
           (fn [[start end s]]
             (accepts? a/backtrack-greedy-find fsm' start end s))
           (partition 3 input-seqs)))

      [2 3 (a/+ a/any) 3 4]
      [3 12 [1 0 1 2 3 0 0 3 1 2 3 4]]

      a/any
      [0 1 [1]
       0 1 [2 3]]

      (a/+ 1)
      [0 2 [1 1]
       1 3 [0 1 1 0]])))

(defn run-fsm [backend fsm f inputs]
  (let [fsm' (a/compile
              [(a/$ :init) fsm]
              {:reducers {:init (constantly []), :conj conj, :conj_ conj}
               :backend backend})]
    (reduce #(f fsm' %1 %2) nil inputs)))

(deftest test-advance
  (doseq [backend backends]
    (testing backend
      (are [fsm input-seqs]
        (let [fsm' (a/compile
                     [(a/$ :init) fsm]
                     {:reducers {:init (constantly []), :conj conj, :conj_ conj}
                      :backend backend})]
          (every?
            (fn [[expected s]]
              (= expected (:value (reduce #(a/advance fsm' %1 %2) nil s))))
            (partition 2 input-seqs)))

        (a/or
          (a/interpose-$ :conj [1 a/any 3])
          [1 2 3])
        [[1 2 3] [1 2 3]
         [1 9 3] [1 9 3]]

        [(a/interpose-$ :conj (a/* a/any))
         (a/interpose-$ :conj [1 2])]
        [[0 1 2] [0 1 2]]

        [(a/interpose-$ :conj (a/* a/any))
         (a/interpose-$ :conj_ [1 2])]
        [[0 1 2] [0 1 2]]

        (a/interpose-$ :conj [1 2 3 4])
        [[1] [1]
         [1 2] [1 2]
         [1 2 3] [1 2 3]
         [1 2 3 4] [1 2 3 4]]

        [1 (a/$ :conj) (a/$ :conj)]
        [[1] [1]]

        [1 a/any (a/$ :conj) 3 4 (a/$ :conj)]
        [[2 4] [1 2 3 4]]

        [(a/or
           (a/interpose-$ :conj [1 2 3])
           [4])
         (a/$ :conj)
         5]
        [[1 2 3] [1 2 3 5]
         [4] [4 5]]

        [1 (a/$ :conj) 2 (a/$ :init) 3 (a/$ :conj) 4 (a/$ :conj)]
        [[1] [1]
         [] [1 2]
         [3] [1 2 3]
         [3 4] [1 2 3 4]]))

    (are [fsm input-seqs]
      (let [fsm' (a/compile
                   [(a/$ :init) fsm]
                   {:reducers {:init (constantly []), :conj conj}
                    :signal inc
                    :backend backend})]
        (every?
          (fn [[expected s]]
            (= expected (:value (reduce #(a/advance fsm' %1 %2) nil s))))
          (partition 2 input-seqs)))

      (a/interpose-$ :conj [1 2 3 4])
      [[0] [0]])))

;;;

#?(:clj (defn- cycle-array [n s]
          (let [cnt (count s)
                ^bytes ary (byte-array n)]
            (dotimes [idx n]
              (aset ary idx (byte (nth s (rem idx cnt)))))
            ary)))

#?(:clj (deftest ^:benchmark benchmark-find
          (let [ary (cycle-array 1e8 [1 2 3])
                fsm (a/compile [1 2 3 4])]
            (println "find within a 100mb buffer")
            (c/quick-bench
              (a/find fsm nil ary)))))
