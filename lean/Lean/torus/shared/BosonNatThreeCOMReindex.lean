import torus.shared.BosonFiniteCertificateNatCOMBasisRankAverage

/-! Finite index rearrangement of the full COM cross trace. The matrices
and the relative cross kernel are arbitrary complex data throughout. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeCOMReindex
open TorusLean.BosonFiniteCertificate Matrix
open scoped BigOperators

theorem k300_COM_trace_reindex (C : Matrix (Fin 1) (Fin 1) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k300COMLevel i=k300COMLevel j then
      (3^(k300COMLevel i)*((k300COMLevel i).factorial:ℂ))*C i j *
      F ⟨k300COMRelativeDegree i,(k300COMIndexLabel i).2⟩
        ⟨k300COMRelativeDegree j,(k300COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k300COMColumn0 a) (k300COMColumn0 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k300COMLevel, k300COMRelativeDegree, k300COMIndexLabel, natCOMRelativeDimension, k300COMColumn0, Fin.sum_univ_succ] <;> dsimp [k300COMRelativeDegree, k300COMIndexLabel] <;> ring

theorem k301_COM_trace_reindex (C : Matrix (Fin 1) (Fin 1) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k301COMLevel i=k301COMLevel j then
      (3^(k301COMLevel i)*((k301COMLevel i).factorial:ℂ))*C i j *
      F ⟨k301COMRelativeDegree i,(k301COMIndexLabel i).2⟩
        ⟨k301COMRelativeDegree j,(k301COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k300COMColumn1 a) (k300COMColumn1 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k301COMColumn1 a) (k301COMColumn1 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k301COMLevel, k301COMRelativeDegree, k301COMIndexLabel, natCOMRelativeDimension, k300COMColumn1, k301COMColumn1, Fin.sum_univ_succ] <;> dsimp [k301COMRelativeDegree, k301COMIndexLabel] <;> ring

theorem k302_COM_trace_reindex (C : Matrix (Fin 2) (Fin 2) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k302COMLevel i=k302COMLevel j then
      (3^(k302COMLevel i)*((k302COMLevel i).factorial:ℂ))*C i j *
      F ⟨k302COMRelativeDegree i,(k302COMIndexLabel i).2⟩
        ⟨k302COMRelativeDegree j,(k302COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*
      C (k300COMColumn2 a) (k300COMColumn2 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k301COMColumn2 a) (k301COMColumn2 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k302COMColumn2 a) (k302COMColumn2 b) *
      F ⟨(⟨2,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k302COMLevel, k302COMRelativeDegree, k302COMIndexLabel, natCOMRelativeDimension, k300COMColumn2, k301COMColumn2, k302COMColumn2, Fin.sum_univ_succ] <;> dsimp [k302COMRelativeDegree, k302COMIndexLabel] <;> ring

theorem k303_COM_trace_reindex (C : Matrix (Fin 3) (Fin 3) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k303COMLevel i=k303COMLevel j then
      (3^(k303COMLevel i)*((k303COMLevel i).factorial:ℂ))*C i j *
      F ⟨k303COMRelativeDegree i,(k303COMIndexLabel i).2⟩
        ⟨k303COMRelativeDegree j,(k303COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*
      C (k300COMColumn3 a) (k300COMColumn3 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*
      C (k301COMColumn3 a) (k301COMColumn3 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k302COMColumn3 a) (k302COMColumn3 b) *
      F ⟨(⟨2,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k303COMColumn3 a) (k303COMColumn3 b) *
      F ⟨(⟨3,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨3,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k303COMLevel, k303COMRelativeDegree, k303COMIndexLabel, natCOMRelativeDimension, k300COMColumn3, k301COMColumn3, k302COMColumn3, k303COMColumn3, Fin.sum_univ_succ] <;> dsimp [k303COMRelativeDegree, k303COMIndexLabel] <;> ring

theorem k304_COM_trace_reindex (C : Matrix (Fin 4) (Fin 4) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k304COMLevel i=k304COMLevel j then
      (3^(k304COMLevel i)*((k304COMLevel i).factorial:ℂ))*C i j *
      F ⟨k304COMRelativeDegree i,(k304COMIndexLabel i).2⟩
        ⟨k304COMRelativeDegree j,(k304COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*
      C (k300COMColumn4 a) (k300COMColumn4 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*
      C (k301COMColumn4 a) (k301COMColumn4 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*
      C (k302COMColumn4 a) (k302COMColumn4 b) *
      F ⟨(⟨2,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k303COMColumn4 a) (k303COMColumn4 b) *
      F ⟨(⟨3,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨3,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k304COMColumn4 a) (k304COMColumn4 b) *
      F ⟨(⟨4,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨4,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k304COMLevel, k304COMRelativeDegree, k304COMIndexLabel, natCOMRelativeDimension, k300COMColumn4, k301COMColumn4, k302COMColumn4, k303COMColumn4, k304COMColumn4, Fin.sum_univ_succ] <;> dsimp [k304COMRelativeDegree, k304COMIndexLabel] <;> ring

theorem k305_COM_trace_reindex (C : Matrix (Fin 5) (Fin 5) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k305COMLevel i=k305COMLevel j then
      (3^(k305COMLevel i)*((k305COMLevel i).factorial:ℂ))*C i j *
      F ⟨k305COMRelativeDegree i,(k305COMIndexLabel i).2⟩
        ⟨k305COMRelativeDegree j,(k305COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*
      C (k300COMColumn5 a) (k300COMColumn5 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*
      C (k301COMColumn5 a) (k301COMColumn5 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*
      C (k302COMColumn5 a) (k302COMColumn5 b) *
      F ⟨(⟨2,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*
      C (k303COMColumn5 a) (k303COMColumn5 b) *
      F ⟨(⟨3,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨3,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k304COMColumn5 a) (k304COMColumn5 b) *
      F ⟨(⟨4,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨4,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k305COMColumn5 a) (k305COMColumn5 b) *
      F ⟨(⟨5,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨5,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k305COMLevel, k305COMRelativeDegree, k305COMIndexLabel, natCOMRelativeDimension, k300COMColumn5, k301COMColumn5, k302COMColumn5, k303COMColumn5, k304COMColumn5, k305COMColumn5, Fin.sum_univ_succ] <;> dsimp [k305COMRelativeDegree, k305COMIndexLabel] <;> ring

theorem k306_COM_trace_reindex (C : Matrix (Fin 7) (Fin 7) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k306COMLevel i=k306COMLevel j then
      (3^(k306COMLevel i)*((k306COMLevel i).factorial:ℂ))*C i j *
      F ⟨k306COMRelativeDegree i,(k306COMIndexLabel i).2⟩
        ⟨k306COMRelativeDegree j,(k306COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(6:ℕ)*((6:ℕ).factorial:ℂ))*
      C (k300COMColumn6 a) (k300COMColumn6 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*
      C (k301COMColumn6 a) (k301COMColumn6 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*
      C (k302COMColumn6 a) (k302COMColumn6 b) *
      F ⟨(⟨2,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*
      C (k303COMColumn6 a) (k303COMColumn6 b) *
      F ⟨(⟨3,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨3,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*
      C (k304COMColumn6 a) (k304COMColumn6 b) *
      F ⟨(⟨4,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨4,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k305COMColumn6 a) (k305COMColumn6 b) *
      F ⟨(⟨5,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨5,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 2, ∑ b : Fin 2,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k306COMColumn6 a) (k306COMColumn6 b) *
      F ⟨(⟨6,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨6,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k306COMLevel, k306COMRelativeDegree, k306COMIndexLabel, natCOMRelativeDimension, k300COMColumn6, k301COMColumn6, k302COMColumn6, k303COMColumn6, k304COMColumn6, k305COMColumn6, k306COMColumn6, Fin.sum_univ_succ] <;> dsimp [k306COMRelativeDegree, k306COMIndexLabel] <;> ring

theorem k307_COM_trace_reindex (C : Matrix (Fin 8) (Fin 8) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k307COMLevel i=k307COMLevel j then
      (3^(k307COMLevel i)*((k307COMLevel i).factorial:ℂ))*C i j *
      F ⟨k307COMRelativeDegree i,(k307COMIndexLabel i).2⟩
        ⟨k307COMRelativeDegree j,(k307COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(7:ℕ)*((7:ℕ).factorial:ℂ))*
      C (k300COMColumn7 a) (k300COMColumn7 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(6:ℕ)*((6:ℕ).factorial:ℂ))*
      C (k301COMColumn7 a) (k301COMColumn7 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*
      C (k302COMColumn7 a) (k302COMColumn7 b) *
      F ⟨(⟨2,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*
      C (k303COMColumn7 a) (k303COMColumn7 b) *
      F ⟨(⟨3,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨3,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*
      C (k304COMColumn7 a) (k304COMColumn7 b) *
      F ⟨(⟨4,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨4,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*
      C (k305COMColumn7 a) (k305COMColumn7 b) *
      F ⟨(⟨5,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨5,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 2, ∑ b : Fin 2,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k306COMColumn7 a) (k306COMColumn7 b) *
      F ⟨(⟨6,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨6,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k307COMColumn7 a) (k307COMColumn7 b) *
      F ⟨(⟨7,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨7,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k307COMLevel, k307COMRelativeDegree, k307COMIndexLabel, natCOMRelativeDimension, k300COMColumn7, k301COMColumn7, k302COMColumn7, k303COMColumn7, k304COMColumn7, k305COMColumn7, k306COMColumn7, k307COMColumn7, Fin.sum_univ_succ] <;> dsimp [k307COMRelativeDegree, k307COMIndexLabel] <;> ring

theorem k308_COM_trace_reindex (C : Matrix (Fin 10) (Fin 10) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ) :
    ((2/3:ℂ) * ∑ i, ∑ j, if k308COMLevel i=k308COMLevel j then
      (3^(k308COMLevel i)*((k308COMLevel i).factorial:ℂ))*C i j *
      F ⟨k308COMRelativeDegree i,(k308COMIndexLabel i).2⟩
        ⟨k308COMRelativeDegree j,(k308COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(8:ℕ)*((8:ℕ).factorial:ℂ))*
      C (k300COMColumn8 a) (k300COMColumn8 b) *
      F ⟨(⟨0,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0,
      ((2/3:ℂ)*3^(7:ℕ)*((7:ℕ).factorial:ℂ))*
      C (k301COMColumn8 a) (k301COMColumn8 b) *
      F ⟨(⟨1,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(6:ℕ)*((6:ℕ).factorial:ℂ))*
      C (k302COMColumn8 a) (k302COMColumn8 b) *
      F ⟨(⟨2,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*
      C (k303COMColumn8 a) (k303COMColumn8 b) *
      F ⟨(⟨3,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨3,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*
      C (k304COMColumn8 a) (k304COMColumn8 b) *
      F ⟨(⟨4,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨4,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*
      C (k305COMColumn8 a) (k305COMColumn8 b) *
      F ⟨(⟨5,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨5,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 2, ∑ b : Fin 2,
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*
      C (k306COMColumn8 a) (k306COMColumn8 b) *
      F ⟨(⟨6,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨6,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1,
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*
      C (k307COMColumn8 a) (k307COMColumn8 b) *
      F ⟨(⟨7,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨7,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) +
    (∑ a : Fin 2, ∑ b : Fin 2,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*
      C (k308COMColumn8 a) (k308COMColumn8 b) *
      F ⟨(⟨8,by decide⟩ : Fin 9),⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ ⟨(⟨8,by decide⟩ : Fin 9),⟨b.val,by simpa [natCOMRelativeDimension] using b.isLt⟩⟩) := by
  norm_num [k308COMLevel, k308COMRelativeDegree, k308COMIndexLabel, natCOMRelativeDimension, k300COMColumn8, k301COMColumn8, k302COMColumn8, k303COMColumn8, k304COMColumn8, k305COMColumn8, k306COMColumn8, k307COMColumn8, k308COMColumn8, Fin.sum_univ_succ] <;> dsimp [k308COMRelativeDegree, k308COMIndexLabel] <;> ring

/-- Exact finite regrouping after true cell orthogonality; arbitrary complex
matrices and cross kernel, with no Hermitian or relative-orthogonality premise. -/
theorem complete_COM_trace_regroup
    (C0 : Matrix (Fin 1) (Fin 1) ℂ)
    (C1 : Matrix (Fin 1) (Fin 1) ℂ)
    (C2 : Matrix (Fin 2) (Fin 2) ℂ)
    (C3 : Matrix (Fin 3) (Fin 3) ℂ)
    (C4 : Matrix (Fin 4) (Fin 4) ℂ)
    (C5 : Matrix (Fin 5) (Fin 5) ℂ)
    (C6 : Matrix (Fin 7) (Fin 7) ℂ)
    (C7 : Matrix (Fin 8) (Fin 8) ℂ)
    (C8 : Matrix (Fin 10) (Fin 10) ℂ)
    (B0 : Matrix (Fin 1) (Fin 1) ℂ)
    (B1 : Matrix (Fin 0) (Fin 0) ℂ)
    (B2 : Matrix (Fin 1) (Fin 1) ℂ)
    (B3 : Matrix (Fin 1) (Fin 1) ℂ)
    (B4 : Matrix (Fin 1) (Fin 1) ℂ)
    (B5 : Matrix (Fin 1) (Fin 1) ℂ)
    (B6 : Matrix (Fin 2) (Fin 2) ℂ)
    (B7 : Matrix (Fin 1) (Fin 1) ℂ)
    (B8 : Matrix (Fin 2) (Fin 2) ℂ)
    (F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ)
    (h0 : ∀ a b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C0 (k300COMColumn0 a) (k300COMColumn0 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C1 (k300COMColumn1 a) (k300COMColumn1 b) +
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*C2 (k300COMColumn2 a) (k300COMColumn2 b) +
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*C3 (k300COMColumn3 a) (k300COMColumn3 b) +
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*C4 (k300COMColumn4 a) (k300COMColumn4 b) +
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*C5 (k300COMColumn5 a) (k300COMColumn5 b) +
      ((2/3:ℂ)*3^(6:ℕ)*((6:ℕ).factorial:ℂ))*C6 (k300COMColumn6 a) (k300COMColumn6 b) +
      ((2/3:ℂ)*3^(7:ℕ)*((7:ℕ).factorial:ℂ))*C7 (k300COMColumn7 a) (k300COMColumn7 b) +
      ((2/3:ℂ)*3^(8:ℕ)*((8:ℕ).factorial:ℂ))*C8 (k300COMColumn8 a) (k300COMColumn8 b) = B0 a b)
    (h1 : ∀ a b : Fin 0,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C1 (k301COMColumn1 a) (k301COMColumn1 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C2 (k301COMColumn2 a) (k301COMColumn2 b) +
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*C3 (k301COMColumn3 a) (k301COMColumn3 b) +
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*C4 (k301COMColumn4 a) (k301COMColumn4 b) +
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*C5 (k301COMColumn5 a) (k301COMColumn5 b) +
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*C6 (k301COMColumn6 a) (k301COMColumn6 b) +
      ((2/3:ℂ)*3^(6:ℕ)*((6:ℕ).factorial:ℂ))*C7 (k301COMColumn7 a) (k301COMColumn7 b) +
      ((2/3:ℂ)*3^(7:ℕ)*((7:ℕ).factorial:ℂ))*C8 (k301COMColumn8 a) (k301COMColumn8 b) = B1 a b)
    (h2 : ∀ a b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C2 (k302COMColumn2 a) (k302COMColumn2 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C3 (k302COMColumn3 a) (k302COMColumn3 b) +
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*C4 (k302COMColumn4 a) (k302COMColumn4 b) +
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*C5 (k302COMColumn5 a) (k302COMColumn5 b) +
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*C6 (k302COMColumn6 a) (k302COMColumn6 b) +
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*C7 (k302COMColumn7 a) (k302COMColumn7 b) +
      ((2/3:ℂ)*3^(6:ℕ)*((6:ℕ).factorial:ℂ))*C8 (k302COMColumn8 a) (k302COMColumn8 b) = B2 a b)
    (h3 : ∀ a b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C3 (k303COMColumn3 a) (k303COMColumn3 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C4 (k303COMColumn4 a) (k303COMColumn4 b) +
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*C5 (k303COMColumn5 a) (k303COMColumn5 b) +
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*C6 (k303COMColumn6 a) (k303COMColumn6 b) +
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*C7 (k303COMColumn7 a) (k303COMColumn7 b) +
      ((2/3:ℂ)*3^(5:ℕ)*((5:ℕ).factorial:ℂ))*C8 (k303COMColumn8 a) (k303COMColumn8 b) = B3 a b)
    (h4 : ∀ a b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C4 (k304COMColumn4 a) (k304COMColumn4 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C5 (k304COMColumn5 a) (k304COMColumn5 b) +
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*C6 (k304COMColumn6 a) (k304COMColumn6 b) +
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*C7 (k304COMColumn7 a) (k304COMColumn7 b) +
      ((2/3:ℂ)*3^(4:ℕ)*((4:ℕ).factorial:ℂ))*C8 (k304COMColumn8 a) (k304COMColumn8 b) = B4 a b)
    (h5 : ∀ a b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C5 (k305COMColumn5 a) (k305COMColumn5 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C6 (k305COMColumn6 a) (k305COMColumn6 b) +
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*C7 (k305COMColumn7 a) (k305COMColumn7 b) +
      ((2/3:ℂ)*3^(3:ℕ)*((3:ℕ).factorial:ℂ))*C8 (k305COMColumn8 a) (k305COMColumn8 b) = B5 a b)
    (h6 : ∀ a b : Fin 2,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C6 (k306COMColumn6 a) (k306COMColumn6 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C7 (k306COMColumn7 a) (k306COMColumn7 b) +
      ((2/3:ℂ)*3^(2:ℕ)*((2:ℕ).factorial:ℂ))*C8 (k306COMColumn8 a) (k306COMColumn8 b) = B6 a b)
    (h7 : ∀ a b : Fin 1,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C7 (k307COMColumn7 a) (k307COMColumn7 b) +
      ((2/3:ℂ)*3^(1:ℕ)*((1:ℕ).factorial:ℂ))*C8 (k307COMColumn8 a) (k307COMColumn8 b) = B7 a b)
    (h8 : ∀ a b : Fin 2,
      ((2/3:ℂ)*3^(0:ℕ)*((0:ℕ).factorial:ℂ))*C8 (k308COMColumn8 a) (k308COMColumn8 b) = B8 a b)
    :
    ((2/3:ℂ) * ∑ i, ∑ j, if k300COMLevel i=k300COMLevel j then
      (3^(k300COMLevel i)*((k300COMLevel i).factorial:ℂ))*C0 i j *
      F ⟨k300COMRelativeDegree i,(k300COMIndexLabel i).2⟩
        ⟨k300COMRelativeDegree j,(k300COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k301COMLevel i=k301COMLevel j then
      (3^(k301COMLevel i)*((k301COMLevel i).factorial:ℂ))*C1 i j *
      F ⟨k301COMRelativeDegree i,(k301COMIndexLabel i).2⟩
        ⟨k301COMRelativeDegree j,(k301COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k302COMLevel i=k302COMLevel j then
      (3^(k302COMLevel i)*((k302COMLevel i).factorial:ℂ))*C2 i j *
      F ⟨k302COMRelativeDegree i,(k302COMIndexLabel i).2⟩
        ⟨k302COMRelativeDegree j,(k302COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k303COMLevel i=k303COMLevel j then
      (3^(k303COMLevel i)*((k303COMLevel i).factorial:ℂ))*C3 i j *
      F ⟨k303COMRelativeDegree i,(k303COMIndexLabel i).2⟩
        ⟨k303COMRelativeDegree j,(k303COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k304COMLevel i=k304COMLevel j then
      (3^(k304COMLevel i)*((k304COMLevel i).factorial:ℂ))*C4 i j *
      F ⟨k304COMRelativeDegree i,(k304COMIndexLabel i).2⟩
        ⟨k304COMRelativeDegree j,(k304COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k305COMLevel i=k305COMLevel j then
      (3^(k305COMLevel i)*((k305COMLevel i).factorial:ℂ))*C5 i j *
      F ⟨k305COMRelativeDegree i,(k305COMIndexLabel i).2⟩
        ⟨k305COMRelativeDegree j,(k305COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k306COMLevel i=k306COMLevel j then
      (3^(k306COMLevel i)*((k306COMLevel i).factorial:ℂ))*C6 i j *
      F ⟨k306COMRelativeDegree i,(k306COMIndexLabel i).2⟩
        ⟨k306COMRelativeDegree j,(k306COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k307COMLevel i=k307COMLevel j then
      (3^(k307COMLevel i)*((k307COMLevel i).factorial:ℂ))*C7 i j *
      F ⟨k307COMRelativeDegree i,(k307COMIndexLabel i).2⟩
        ⟨k307COMRelativeDegree j,(k307COMIndexLabel j).2⟩ else 0) +
    ((2/3:ℂ) * ∑ i, ∑ j, if k308COMLevel i=k308COMLevel j then
      (3^(k308COMLevel i)*((k308COMLevel i).factorial:ℂ))*C8 i j *
      F ⟨k308COMRelativeDegree i,(k308COMIndexLabel i).2⟩
        ⟨k308COMRelativeDegree j,(k308COMIndexLabel j).2⟩ else 0) =
    (∑ a : Fin 1, ∑ b : Fin 1, B0 a b * F ⟨(⟨0,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨0,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 0, ∑ b : Fin 0, B1 a b * F ⟨(⟨1,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨1,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1, B2 a b * F ⟨(⟨2,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨2,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1, B3 a b * F ⟨(⟨3,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨3,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1, B4 a b * F ⟨(⟨4,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨4,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1, B5 a b * F ⟨(⟨5,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨5,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 2, ∑ b : Fin 2, B6 a b * F ⟨(⟨6,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨6,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 1, ∑ b : Fin 1, B7 a b * F ⟨(⟨7,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨7,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) +
    (∑ a : Fin 2, ∑ b : Fin 2, B8 a b * F ⟨(⟨8,by decide⟩ : Fin 9),⟨(a).val,by simpa [natCOMRelativeDimension] using (a).isLt⟩⟩ ⟨(⟨8,by decide⟩ : Fin 9),⟨(b).val,by simpa [natCOMRelativeDimension] using (b).isLt⟩⟩) := by
  rw [k300_COM_trace_reindex, k301_COM_trace_reindex, k302_COM_trace_reindex, k303_COM_trace_reindex, k304_COM_trace_reindex, k305_COM_trace_reindex, k306_COM_trace_reindex, k307_COM_trace_reindex, k308_COM_trace_reindex]
  simp_rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

end TorusLean.Shared.BosonNatThreeCOMReindex
