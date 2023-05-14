Derivation : Γ₁ , P ↝ Q ¦ plan
Derivation = weakening P (from-yes (decSub P P')) tt
             (composition
               (weakComp (from-yes (decSub (((+ , ontable b) ∷ (+ , clear b) ∷ (+ , clear a) ∷ (- , handempty) ∷ (- , ontable a) ∷ (+ , holding a) ∷ []))
                                                ((- , ontable a) ∷ (+ , ontable b) ∷ (+ , clear a) ∷ (+ , holding a) ∷ (+ , clear b) ∷ [])))
                 (frame + (ontable b) (λ x → x) (λ x → x) (frame + (clear b) (λ x → x) (λ x → x) (applyAction tt tt tt)))
                 (frame - (ontable a) (λ x → x) (λ x → x) (frame + (ontable b) (λ x → x) (λ x → x) (frame + (clear a) (λ x → x) (λ x → x) (applyAction tt tt tt)))))
           (shrink tt tt (from-yes (decSub ((- , ontable a) ∷ (+ , ontable b) ∷ (+ , clear a) ∷ (- , holding a) ∷ (- , clear b) ∷ (+ , on a b) ∷ (+ , handempty) ∷ []) Q))))


Derivation : Γ₁ , P ↝ Q ¦ plan
Derivation = weakening P (from-yes (decSub P P')) tt (composition 
        (weakComp (from-yes (decSub ((+ , ontable b) ∷ (+ , clear b) ∷ (+ , clear a) ∷ (- , handempty) ∷ (- , ontable a) ∷ (+ , holding a) ∷ [])
        ((- , ontable a) ∷ (+ , ontable b) ∷ (+ , clear a) ∷ (+ , holding a) ∷ (+ , clear b) ∷ [])))
        ((frame + (ontable b) (λ z → z) (λ z → z) (frame + (clear b) (λ z → z) (λ z → z) (applyAction tt tt tt))))
        ((frame - (ontable a) (λ z → z) (λ z → z) (frame + (ontable b) (λ z → z) (λ z → z) (frame + (clear a) (λ z → z) (λ z → z) (applyAction tt tt tt))))))
        (shrink tt tt (from-yes (decSub Q ((- , ontable a) ∷ (+ , ontable b) ∷ (+ , clear a) ∷ (- , holding a) ∷ (- , clear b) ∷ (+ , on a b) ∷ (+ , handempty) ∷ [])))))

