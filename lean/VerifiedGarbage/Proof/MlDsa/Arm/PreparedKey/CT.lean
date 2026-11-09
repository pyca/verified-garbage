module

public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Entry
public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Body
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.CopyTr
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on ARMv7, preparing keys: constant time

Two runs in the same layout leak the same: the copy and the calls leak only
the addresses of the buffers (`body_tr`), and the frame, the moves and the
loads of the registers saved only the stack pointer (`entry_tr`). So the
preparations leak nothing beyond their pointers and stack pointer, which is
all their contracts make public.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.PreparedKey

open VG VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.PreparedKey
open VG.Impl.MlDsa.Arm.Sign (Prims Ptr callR callS copy seqR)
open VG.Proof.MlDsa.Arm.Sign
open VG.Spec.Sha3 (bytesAt)

/-! ## The body -/

section
variable {D bytes count : Nat}

/-- Two runs in the same layout. -/
abbrev Rel (D bytes count : Nat) : State → State → Prop := LRel D (input bytes) (output bytes count)

theorem copy_rel (hb : 0 < bytes) :
    RelCT isa (Rel D bytes count) (copy (.r8, 0) (.r4, 0) bytes) (Rel D bytes count) :=
  postDep (copy_tr (by decide) (by decide) fun x y R =>
      ⟨R.regs (.r8, bytes + 1024 * count) (List.mem_append_right _ (List.mem_cons_self ..)),
        R.regs (.r4, bytes) (List.mem_append_left _ (List.mem_cons_self ..))⟩)
    (fun x y R => ⟨copy_okB R.lx (copy_check bytes count hb), copy_okB R.ly (copy_check bytes count hb)⟩)
    fun _ _ _ _ R ⟨hx, _⟩ ⟨hy, _⟩ => R.post (bases_io _ _) hx hy

/-- What a call that writes a polynomial at `o` leaves for the `NTT` of it. -/
abbrev RelR (D bytes count o : Nat) (x y : State) : Prop :=
  Rel D bytes count x y ∧ Reduced x.mem (pa x (.r8, o)) ∧ Reduced y.mem (pa y (.r8, o))

theorem red_after {s s' : State} {o : Nat} {f : Poly} (hP : PPostB D s s' [((.r8, o), 1024)])
    (h : PolyIs s'.mem (pa s (.r8, o)) f) : Reduced s'.mem (pa s' (.r8, o)) := by
  rw [hP.pa (show Reg.r8 ∈ bases by decide)]; exact h.1

variable {P : Prims} (hP : PrimsOk P D)
include hP

theorem transform_rel {o : Nat}
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, o) (.r7, 0) = true) :
    RelCT isa (RelR D bytes count o) (transform P o) (Rel D bytes count) :=
  postDep (ipAtW_tr hP.ntt hi) (fun _ _ ⟨R, rx, ry⟩ => ⟨ipAtW_ok hP.ntt R.lx hi rx, ipAtW_ok hP.ntt R.ly hi ry⟩)
    fun _ _ _ _ ⟨R, _, _⟩ ⟨hx, _⟩ ⟨hy, _⟩ => R.post (bases_io _ _) hx hy

omit hP in
theorem publicPoly_rel (C1 : Callee (fun S => unpackT1Contract Arm.abi S) 0 D Impl.MlDsa.Arm.Pack.unpackT1)
    (hP : PrimsOk P D) {p : Params} {i : Nat}
    (hc : rwChk (input bytes ++ output bytes count) (output bytes count) (.r4, 32 + 320 * i) 320
      (.r8, p.pkLen + 1024 * i) 1024 = true)
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, p.pkLen + 1024 * i) (.r7, 0) = true) :
    RelCT isa (Rel D bytes count) (publicPoly P p i) (Rel D bytes count) := by
  unfold publicPoly
  exact RelCT.seq (postDep (t1At_tr C1 hc) (fun x y R => ⟨t1At_ok C1 R.lx hc, t1At_ok C1 R.ly hc⟩)
    fun _ _ _ _ R ⟨hx, _, px⟩ ⟨hy, _, py⟩ => ⟨R.post (bases_io _ _) hx hy, red_after hx px, red_after hy py⟩)
    (transform_rel hP hi)

theorem secretPoly_rel {p : Params} {i : Nat} {src len a b : Nat} (he : secretPiece p i = (src, len, a, b))
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hc : rwChk (input bytes ++ output bytes count) (output bytes count) (.r4, src) len
      (.r8, p.skLen + 1024 * i) 1024 = true)
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, p.skLen + 1024 * i) (.r7, 0) = true) :
    RelCT isa (Rel D bytes count) (secretPoly P p i) (Rel D bytes count) := by
  unfold secretPoly
  rw [he]
  exact RelCT.seq (postDep (bupAt_tr hP hab hl hc) (fun x y R => ⟨bupAt_ok hP R.lx hab hl hc,
      bupAt_ok hP R.ly hab hl hc⟩)
    fun _ _ _ _ R ⟨hx, _, px⟩ ⟨hy, _, py⟩ => ⟨R.post (bases_io _ _) hx hy, red_after hx px, red_after hy py⟩)
    (transform_rel hP hi)

end

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D)
include hP

theorem public_rel (C1 : Callee (fun S => unpackT1Contract Arm.abi S) 0 D Impl.MlDsa.Arm.Pack.unpackT1)
    {p : Params} (hp : Ok3 p) :
    RelCT isa (Rel D p.pkLen p.k) (.seq (copy (.r8, 0) (.r4, 0) p.pkLen) (seqR (publicPoly P p) 0 p.k))
      (Rel D p.pkLen p.k) := by
  have hpk := pk_eq hp
  refine RelCT.seq (copy_rel (by omega)) ?_
  have := seqR_tr (f := publicPoly P p) (R := fun _ => Rel D p.pkLen p.k) p.k 0 fun i _ hi => by
    obtain ⟨hc, hi'⟩ := public_checks hp (i := i) (by omega)
    exact publicPoly_rel C1 hP hc hi'
  exact this

theorem secret_rel {p : Params} (hp : Ok3 p) :
    RelCT isa (Rel D p.skLen (p.ℓ + 2 * p.k))
      (.seq (copy (.r8, 0) (.r4, 0) p.skLen) (seqR (secretPoly P p) 0 (p.ℓ + 2 * p.k)))
      (Rel D p.skLen (p.ℓ + 2 * p.k)) := by
  have hsk : 0 < p.skLen := by rcases hp with rfl | rfl | rfl <;> decide
  refine RelCT.seq (copy_rel hsk) ?_
  have := seqR_tr (f := secretPoly P p) (R := fun _ => Rel D p.skLen (p.ℓ + 2 * p.k)) (p.ℓ + 2 * p.k) 0
    fun i _ hi => by
      have hi' : i < p.ℓ + 2 * p.k := by omega
      obtain ⟨src, len, a, b, he⟩ : ∃ src len a b, secretPiece p i = (src, len, a, b) := by
        rcases secretPiece p i with ⟨src, len, a, b⟩
        exact ⟨src, len, a, b, rfl⟩
      have hchecks := secret_checks hp hi'
      rw [he] at hchecks
      obtain ⟨hc, hab, hl⟩ := hchecks
      exact secretPoly_rel hP he hab hl hc (ip_check _ _ (by omega))
  exact this

end

/-! ## The entry -/

theorem ldrSp_tr {r : Reg} {off : Nat} {P : State → State → Prop} (hP : ∀ x y, P x y → x.sp = y.sp) :
    RelCT isa P (.block [.ldrSp r off]) fun x y => x.sp = y.sp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  refine ⟨?_, show s₁'.sp = s₂'.sp by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hP _ _ hp]⟩
  rw [Exec.block_iff] at e₁ e₂
  rw [ldrSp_leak e₁, ldrSp_leak e₂, hP _ _ hp]

theorem movs_nomem :
    ∀ i ∈ ([.mov .r4 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r2)] : List Instr), ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

/-- The entry states of two runs: preconditions and public data. -/
abbrev Ent2 (bytes count : Nat) (x y : State) : Prop :=
  EntryPre bytes count x ∧ EntryPre bytes count y ∧ x.sp = y.sp ∧ x.gpr .r0 = y.gpr .r0 ∧
    x.gpr .r1 = y.gpr .r1 ∧ x.gpr .r2 = y.gpr .r2

theorem entry_tr {body : Prog isa} {bytes count : Nat} (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hbody : RelCT isa (Rel callStack bytes count) body (Rel callStack bytes count)) :
    RelCT isa (Ent2 bytes count) (entry body) fun _ _ => True := by
  unfold entry
  refine RelCT.frame (fun s₁ s₂ h => h.2.2.1) ?_
  refine RelCT.mono (P := fun a b => ∃ q : State × State, Ent2 bytes count q.1 q.2 ∧
      a = pushed saved q.1 ∧ b = pushed saved q.2) ?_
    (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ⟨(s₁, s₂), hp, Argon2.Arm.push_eq (by decide) pa,
      Argon2.Arm.push_eq (by decide) pb⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun ⟨σ₁, σ₂⟩ => ?_
  let F (σ u : State) : Prop :=
    u.gpr .r4 = σ.gpr .r0 ∧ u.gpr .r8 = σ.gpr .r1 ∧ u.gpr .r7 = σ.gpr .r2 ∧ u.sp = σ.sp - BitVec.ofNat 32 16 ∧
      u.rd = σ.rd ∧ u.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr
  have mv : ∀ σ : State, WP isa (.block [.mov .r4 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r2)])
      (pushed saved σ) (F σ) := fun σ =>
    WP.mono (movs_ok _) fun u ⟨g4, g8, g7, _, _, grd, gwr, gsp⟩ =>
      ⟨by rw [g4, pushed_gpr], by rw [g8, pushed_gpr], by rw [g7, pushed_gpr], by rw [gsp, pushed_sp]; rfl,
        by rw [grd, pushed_rd], by rw [gwr, pushed_wr]; rfl⟩
  refine RelCT.seq (RelCT.wp (F₁ := fun u => Ent2 bytes count σ₁ σ₂ ∧ F σ₁ u) (F₂ := F σ₂)
    (block_nomem_tr movs_nomem) fun a b ⟨h, ha, hb⟩ => ⟨ha ▸ WP.mono (mv σ₁) fun _ e => ⟨h, e⟩, hb ▸ mv σ₂⟩) ?_
  refine RelCT.seq (RelCT.mono hbody (fun x y ⟨_, ⟨h, f₁⟩, f₂⟩ => ?_) fun _ _ h => h) ?_
  · obtain ⟨h₁, h₂, psp, p0, p1, p2⟩ := h
    obtain ⟨x4, x8, x7, xsp, xrd, xwr⟩ := f₁
    obtain ⟨y4, y8, y7, ysp, yrd, ywr⟩ := f₂
    refine ⟨entry_lay h₁ hb ho x4 x8 x7 xsp xrd xwr, entry_lay h₂ hb ho y4 y8 y7 ysp yrd ywr, fun b hb' => ?_,
      by rw [xsp, ysp, psp]⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    · rw [x4, y4, p0]
    · rw [x8, y8, p1]
    · rw [x7, y7, p2]
  · exact RelCT.seq (ldrSp_tr fun x y h => h.sp) (RelCT.seq (ldrSp_tr fun x y h => h)
      (RelCT.mono (ldrSp_tr fun x y h => h) (fun _ _ h => h) fun _ _ _ => trivial))

end VG.Proof.MlDsa.Arm.PreparedKey
