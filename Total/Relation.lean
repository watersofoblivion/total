def Relation (α: Type): Type := α → α → Prop

namespace Relation
  def deterministic {α: Type} (R: Relation α): Prop :=
    ∀ {x y₁ y₂: α}, R x y₁ → R x y₂ → y₁ = y₂

  def normal {α: Type} (R: Relation α) (x₁: α): Prop := ¬ ∃ x₂: α, R x₁ x₂
end Relation

inductive RTC {α: Type} (R: Relation α): Relation α where
  | refl {x: α}: RTC R x x
  | trans {x y z: α}: R x y → RTC R y z → RTC R x z

namespace RTC
  theorem brecOn {α} {R: Relation α} {motive : {x y: α} → RTC R x y → Prop} {x y: α} (t: RTC R x y) (ip: {x y: α} → (t: RTC R x y) → @RTC.below _ _ @motive _ _ t → motive t): motive t :=
    RTC.rec (motive := fun _ _ r => RTC.below r ∧ motive r)
      ⟨RTC.below.refl, ip _ RTC.below.refl⟩
      (fun hxy hyz ⟨p₁, p₂⟩ =>
        let b := RTC.below.trans hxy p₁ p₂
        ⟨b, ip (RTC.trans hxy hyz) b⟩)
      t
      |>.right
end RTC

instance {α: Type} (R: Relation α): Trans R R (RTC R) where
  trans {x y z: α}: R x y → R y z → RTC R x z
    | hxy, hyz => .trans hxy (.trans hyz .refl)

instance {α: Type} (R: Relation α): Trans R (RTC R) (RTC R) where
  trans {x y z: α}: R x y → RTC R y z → RTC R x z
    | hxy, hyz => .trans hxy hyz

instance {α: Type} (R: Relation α): Trans (RTC R) R (RTC R) where
  trans hxy hyz := by
    induction hxy with
      | refl           => exact .trans hyz .refl
      | trans hxy _ ih => exact .trans hxy (ih hyz)

  -- trans {x y z: α}: RTC R x y → R y z → RTC R x z
  --   | .refl,            hyz => .trans hyz .refl
  --   | .trans hxy' hy'y, hyz =>
  --     have ih := trans hxy' hy'y
  --     .trans hxy' ih

instance {α: Type} (R: Relation α): Trans (RTC R) (RTC R) (RTC R) where
  trans hxy hyz := by
    induction hxy with
      | refl           => exact hyz
      | trans hxy _ ih => exact .trans hxy (ih hyz)

  -- trans {x y z: α}: RTC R x y → RTC R y z → RTC R x z
  --     | .refl,            hyz   => hyz
  --     | .trans hyy' hy'y, hyz   =>
  --       have ih := trans hyy' hy'y
  --       .trans ih hyz
