(ns automat.compiler.backtrack
  (:refer-clojure :exclude [compile])
  (:require
   [automat.compiler.core :as core :refer #?(:clj []
                                             :cljs [ICompiledAutomaton CompiledAutomatonState])]
   [automat.fsm :as fsm]
   [automat.stream :as stream])
  #?(:clj (:import
           [automat.compiler.core
            ICompiledAutomaton
            CompiledAutomatonState])))

(def is-identical? #?(:clj identical? :cljs keyword-identical?))

(defn- default-match-fn [transition-map input]
  (when-let [state (get transition-map input)]
    [state input]))

(declare ^:private find-advance-inter)

(defn- find-default-way [fsm begin-state-index state-index start-index stream-index value stream  signal match-fn reducers original-input]
  (let [s2  (get-in fsm [:state->input->state state-index fsm/default])
                value' (if s2
                         (->> (concat
                               (get-in fsm [:state->input->actions state-index fsm/pre])
                               (get-in fsm [:state->input->actions state-index fsm/default]))
                              distinct
                              (map reducers)
                              (remove nil?)
                              (reduce #(%2 %1 original-input) value))
                         value)]
            (if (or (nil? s2) (is-identical? fsm/reject s2))
              (if (= state-index begin-state-index)
                (find-advance-inter fsm begin-state-index state-index (inc stream-index)
                                    (inc stream-index) value stream signal match-fn
                                    reducers)
                ::reject)
              (if (contains? (:accept fsm) s2)
                (CompiledAutomatonState.
                 true
                 nil
                 s2
                 start-index
                 (inc stream-index)
                 value')
                (find-advance-inter fsm begin-state-index (long s2) start-index (inc stream-index) value' stream signal match-fn reducers)))))

(defn- find-advance-inter
  "算法：
  1. 依据当前状态、当前输入获取取下一个状态s1和实际输入a1，计算转移到下一个状态过程中得到的值v1
  2. 如果s1为nil或reject，则7
  3. 如果s1为结束状态，返回结束状态和值v1组成状态对象
  4. 其他情况，以s1做当前状态，下一个输入做当前输入，递归向前find-advance-inter,结果放入sr
  5. 如果sr为结束状态，返回结束状态和值
  6. 如果sr为非结束状态（包括nil），则7
  7. 依据当前状态、default获取下一个状态s2和实际输入default, 计算值v2
  8. 如果s2为nil或reject，返回nil
  9. 如果s2为结束状态，返回结束状态和值v2组成状态对象
  10. 其他情况，以s2做当前状态，下一个输入做当前输入，find-advance-inter的结果放入sr2
  11. 如果sr2为结束状态，返回sr2
  12. 以当前状态，下一个输入做当前输入，返回find-advance-inter"
  [fsm begin-state-index state-index start-index stream-index value stream signal match-fn reducers]
  (let [;;original-input (stream/next-input stream ::eof) ;; 此处因流没法回溯，所以应该改为数组
        original-input (nth stream stream-index ::eof)
        input (signal original-input)]
    (if (is-identical? ::eof input)
      (CompiledAutomatonState.
       (contains? (:accept fsm) state-index)
       nil
       state-index
       start-index
       stream-index
       value)
      (let [transition-map (get-in fsm [:state->input->state state-index])
            [s1 actual-input] (match-fn transition-map input)
            value' (if s1
                     (->> (concat
                           (get-in fsm [:state->input->actions state-index fsm/pre])
                           (get-in fsm [:state->input->actions state-index actual-input]))
                          distinct
                          (map reducers)
                          (remove nil?)
                          (reduce #(%2 %1 original-input) value))
                     value)]
        (if (or (nil? s1) (is-identical? s1 fsm/reject))
          (find-default-way fsm begin-state-index state-index start-index stream-index value stream signal match-fn reducers original-input)
          (if (contains? (:accept fsm) s1)
            (CompiledAutomatonState.
             true
             nil
             s1
             start-index
             (inc stream-index)
             value')
            (let [^CompiledAutomatonState sr (find-advance-inter fsm begin-state-index (long s1) start-index (inc stream-index) value' stream signal match-fn reducers)]
              (if (and sr (not= ::reject sr) (.-accepted? sr))
                sr
                (find-default-way fsm begin-state-index state-index start-index stream-index value stream signal match-fn reducers original-input)))))))))

(defn- find-advance [fsm ^CompiledAutomatonState state stream signal match-fn reducers]
  (let [signal #(if (is-identical? % ::eof) % (signal %))
        stream (stream/to-stream stream)
        stream (for [x (repeatedly #(stream/next-input stream ::eof))
                     :while (not= x ::eof)]
                 x)
        stream (-> stream vec (conj ::eof))
        sr (find-advance-inter fsm
                               (.-state-index state)
                               (.-state-index state)
                               (.-start-index state)
                               (.-stream-index state)
                               (.-value state)
                               stream
                               signal
                               match-fn
                               reducers)]
    (if (or (nil? sr) (is-identical? sr ::reject))
      state
      sr)))

(defn- advance [fsm state stream signal match-fn reducers restart?]
  (let [signal #(if (is-identical? % ::eof) % (signal %))
        ^CompiledAutomatonState original-state state
        stream (stream/to-stream stream)
        original-stream-index (.-stream-index original-state)]
    (loop [original-input (stream/next-input stream ::eof)
           value (.-value original-state)
           state (.-state-index original-state)
           start-index (.-start-index original-state)
           stream-index original-stream-index]

      (let [input (signal original-input)]
        (if (is-identical? ::eof input)

          (if (== original-stream-index stream-index)
            original-state
            (CompiledAutomatonState.
             (contains? (:accept fsm) state)
             nil
             state
             start-index
             stream-index
             value))

          (let [transition-map (get-in fsm [:state->input->state state])
                [state'' actual-input] (match-fn transition-map input)
                state'  (or state'' (get-in fsm [:state->input->state state fsm/default]))
                default? (not (identical? state'' state'))
                value' (if state'
                         (->> (concat
                               (get-in fsm [:state->input->actions state fsm/pre])
                               (when-not default?
                                 (get-in fsm [:state->input->actions state actual-input]))
                               (when default?
                                 (get-in fsm [:state->input->actions state fsm/default])))
                              distinct
                              (map reducers)
                              (remove nil?)
                              (reduce #(%2 %1 original-input) value))
                         value)
                stream-index' (if (= state 0)
                                (inc stream-index)
                                stream-index)]

            (cond
              (or (nil? state') (is-identical? fsm/reject state'))
              (if restart?
                (recur
                 (if (= state 0)
                   (stream/next-input stream ::eof)
                   original-input)
                 value'
                 0
                 stream-index'
                 stream-index')
                ::reject)

              (contains? (:accept fsm) state')
              (CompiledAutomatonState.
               true
               nil
               state'
               start-index
               (inc stream-index)
               value')

              :else
              (recur
               (stream/next-input stream ::eof)
               value'
               (long state')
               start-index
               (inc stream-index)))))))))

(defn compile
  [fsm {:keys [reducers signal action-comparator match-fn]
        :or {signal identity
             match-fn default-match-fn}}]
  {:pre [(core/precompiled-automaton? fsm)]}
  (let [initially-accepted? (contains? (:accept fsm) 0)]
    (with-meta
      (reify ICompiledAutomaton
        (start [_ initial-value]
          (CompiledAutomatonState.
           initially-accepted?
           nil
           0
           0
           0
           initial-value))
        (find [this state stream]
          (let [state (core/->automaton-state this state)]
            (if (.-accepted? ^CompiledAutomatonState state)
              state
              #_(advance fsm state stream signal match-fn reducers true)
              (find-advance fsm state stream signal match-fn reducers))))
        (advance-stream [this state stream reject-value]
          (let [state (core/->automaton-state this state)
                state' (advance fsm state stream signal match-fn reducers false)]
            (if (is-identical? ::reject state')
              reject-value
              state'))))
      {:fsm (-> fsm meta :fsm)})))
