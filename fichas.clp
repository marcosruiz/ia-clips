;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;   MARCOS RUIZ GARCÍA, 648045    ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;           MODULO MAIN           ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmodule MAIN
	(export deftemplate nodo)
	(export deffunction heuristica))

(deftemplate MAIN::nodo
   (multislot estado)
   (multislot camino)
   (slot heuristica)
	 (slot coste)
   (slot clase (default abierto)))

(defglobal MAIN
   ?*estado-inicial* = (create$ B B B H V V V)
   ?*estado-final* = (create$ V V V H B B B))

; H1: numero de piezas B situadas a la izquierda de las piezas V
(deffunction MAIN::heuristica ($?estado)
  (bind ?res 0)
	(loop-for-count (?i 1 7)
		(bind ?ficha (nth ?i $?estado))
		(if (eq ?ficha V)
			then
				(loop-for-count (?j 1 ?i)
					(if (eq ?j B)
						then(bind ?res (+ ?res 1))
					)
				)
		)
	)
?res)

;;; H2: numero de piezas descolocadas
;(deffunction MAIN::heuristica ($?estado)
;   (bind ?res 0)
;   (loop-for-count (?i 1 7)
;    (if (neq (nth ?i $?estado)
;             (nth ?i ?*estado-final*))
;         then (bind ?res (+ ?res 1))
;     )
;    )
;   ?res)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     MODULO MAIN::INICIAL        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule MAIN::inicial
   =>
   (assert (nodo
              (estado ?*estado-inicial*)
              (camino)
              (heuristica (heuristica ?*estado-inicial*))
							(coste 0)
              (clase abierto)))
 )

(defrule MAIN::pasa-el-mejor-a-cerrado
   ?nodo <- (nodo (clase abierto)
	 								(coste ?c1)
                  (heuristica ?h1))
   (not (nodo (clase abierto)
	 						(coste ?c2)
              (heuristica ?h2&:(< (+ ?h2 ?c2) (+ ?h1 ?c1)))))
=>
   (modify ?nodo (clase cerrado))
	 (focus OPERACIONES))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; MODULO MAIN::OPERACIONES        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmodule OPERACIONES (import MAIN deftemplate nodo)
(import MAIN deffunction heuristica))


;;; movemos H a la izquierda
(defrule OPERACIONES::izquierda
   (nodo (estado $?x ?f $?y&:(<= (length $?y) 2) H $?z)
        	(camino $?movimientos)
					(coste ?coste)
          (clase cerrado))
=>
(bind $?nuevo-estado (create$ $?x H $?y ?f $?z))
   (assert (nodo
		      (estado $?nuevo-estado)
              (camino $?movimientos (implode$ ?nuevo-estado))
							(coste (+ ?coste 1))
              (heuristica (heuristica $?nuevo-estado)))))

;;; movemos H a la derecha
(defrule OPERACIONES::derecha
   (nodo (estado $?x H $?y&:(<= (length $?y) 2) ?f $?z)
          (camino $?movimientos)
					(coste ?coste)
          (clase cerrado))
 =>
 (bind $?nuevo-estado (create$ $?x ?f $?y H $?z))
   (assert (nodo
		      (estado $?nuevo-estado)
              (camino $?movimientos (implode$ ?nuevo-estado))
							(coste (+ ?coste 1))
              (heuristica (heuristica $?nuevo-estado)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;      MODULO RESTRICCIONES       ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmodule RESTRICCIONES
   (import MAIN deftemplate nodo))

(defrule RESTRICCIONES::repeticiones-de-nodo
   (declare (auto-focus TRUE))
   (nodo (estado $?actual)
         (camino $?movimientos-1))
   ?nodo <- (nodo (estado $?actual)
                  (camino $?movimientos-2&:(> (length ?movimientos-2) (length ?movimientos-1))))
 =>
   (retract ?nodo))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;    MODULO MAIN::SOLUCION        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmodule SOLUCION
   (import MAIN deftemplate nodo))

(defrule SOLUCION::reconoce-solucion
   (declare (auto-focus TRUE))
   ?nodo <- (nodo (estado V V V H B B B)
               (camino $?movimientos)
							 (coste ?coste-sol))
 =>
   (retract ?nodo)
   (assert (solucion $?movimientos ?coste-sol)))

(defrule SOLUCION::escribe-solucion
   (solucion $?movimientos ?coste-sol)
  =>
	(bind ?lon (length $?movimientos))
   (printout t "Solucion:" crlf)
	 (loop-for-count (?i 1 ?lon)
	 		(printout t (nth ?i $?movimientos) crlf)
	)
	(printout t crlf "Coste: " ?coste-sol crlf)
   (halt))
