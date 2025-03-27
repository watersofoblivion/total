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
  /-!
  Workaround for https://github.com/leanprover/lean4/issues/1672
  -/

  /--
  Hand-implement the standard inductive `brecOn` theorem.
  -/
  theorem brecOn {α} {R: Relation α} {motive : {x y: α} → RTC R x y → Prop} {x y: α} (on: RTC R x y) (ip: {x y: α} → (on: RTC R x y) → @RTC.below _ _ @motive _ _ on → motive on): motive on :=
    have ⟨_, motive⟩ := RTC.recOn (motive := fun _ _ rtc => RTC.below rtc ∧ motive rtc)
      on
      ⟨RTC.below.refl, ip _ RTC.below.refl⟩
      (fun hxy hyz rtc =>
        let below := RTC.below.trans hxy rtc.left rtc.right
        ⟨below, ip (RTC.trans hxy hyz) below⟩)
    motive
end RTC

instance {α: Type} (R: Relation α): Trans R R (RTC R) where
  trans {x y z: α}: R x y → R y z → RTC R x z
    | hxy, hyz => .trans hxy (.trans hyz .refl)

instance {α: Type} (R: Relation α): Trans R (RTC R) (RTC R) where
  trans {x y z: α}: R x y → RTC R y z → RTC R x z
    | hxy, hyz => .trans hxy hyz

instance {α: Type} (R: Relation α): Trans (RTC R) R (RTC R) where
  trans {x y z: α} (h₁: RTC R x y) (h₂: R y z): RTC R x z :=
    trans h₁ h₂
    where
      trans {x y z: α}: RTC R x y → R y z → RTC R x z
        | .refl,            hyz => .trans hyz .refl
        | .trans hxy' hy'y, hyz =>
          have ih := trans hy'y hyz
          .trans hxy' ih

instance {α: Type} (R: Relation α): Trans (RTC R) (RTC R) (RTC R) where
  trans {x y z: α} (h₁: RTC R x y) (h₂: RTC R y z): RTC R x z :=
    trans h₁ h₂
    where
      trans {x y z: α}: RTC R x y → RTC R y z → RTC R x z
        | .refl,            hyz   => hyz
        | .trans hxy' hy'y, hyz   =>
          have ih := trans hy'y hyz
          .trans hxy' ih
