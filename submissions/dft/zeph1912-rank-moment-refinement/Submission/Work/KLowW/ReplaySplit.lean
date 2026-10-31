import Submission.Work.KLowW.ScalK

/- Proof-engineering adapter for checking the unchanged native replay in
segments. No circuit, event list, checkpoint, or checker definition is changed. -/

namespace KLW

theorem evsS_append (q : SPw) (o : Bool) (xs ys : List WEv)
    (R : RT) (k : RT → Bool) :
    evsS q o (xs ++ ys) R k =
      evsS q o xs R (fun S => evsS q o ys S k) := by
  induction xs generalizing R with
  | nil => rfl
  | cons e es ih =>
    change evS q o e R (fun S => evsS q o (es ++ ys) S k) =
      evS q o e R (fun S => evsS q o es S (fun U => evsS q o ys U k))
    apply congrArg (evS q o e R)
    funext S
    exact ih S

end KLW

#print axioms KLW.evsS_append
