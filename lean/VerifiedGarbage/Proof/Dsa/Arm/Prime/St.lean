module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Sk
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Rsa.BoolNat

/-! # An RSA key on ARMv7: the operations as pieces

`St P E A L V LS`: a stage (`KS`) with the working space's registers (`Ws`),
the values `A σ` and `V σ` given by the state `σ` the body starts from. The
operations of the key working space as pieces (`VP`): correct from any such
stage, and leaking the same in two runs at it, by the taint analysis of each
piece (`Cert`) with `r7`–`r9` public. Flags are `b2n` of booleans.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)
open VG.Proof.Rsa (b2n)
open VG.Impl.RsaKeyGen.Arm.Key (notS andNotS isOne)
open VG.Proof.RsaKeyGen.Arm.Key (b2n_xor b2n_and b2n_or b2n_mod2 b2n_eq_one b2n_lt)

/-- A stage with the working space's registers. -/
abbrev St (P : CP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (V σ) LS s ∧ Ws s P.B P.Z P.W nArr

/-- A piece the taint analysis checks with the working space's registers public. -/
theorem VP.kv {F G : State → State → Prop} {c : Prog isa} {P : CP} (cert : Cert c)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z P.W nArr) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    have w₁ := hws _ _ h₁; have w₂ := hws _ _ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]) wp

section
variable {P : CP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- A step that writes `[o] := x` alone, and header words `ds`. -/
theorem KS.write1 {o x : Nat} {ds : List Nat} (h : KS P σ A live V ls s)
    (k : Keep P.B P.W [o] ds s.mem t.mem) (ho : o < nArr) (hds : ∀ d ∈ ds, SlotOk d)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (e : num t.mem P.B P.W o = x)
    (hls : ∀ d ∈ ls, d ∉ ds) : KS P σ (upd A o x) (o :: live) V ls t := by
  refine h.core k (by simpa using ho) hds sp rd wr (fun j hj => ?_) (h.sl_keep k hds hls) (fun j hj => ?_) h.ls_ok
  · by_cases hjo : j = o
    · subst hjo; rw [upd_self]; exact e
    · have hj' : j ∈ live := (List.mem_cons.mp hj).resolve_left hjo
      rw [upd_ne _ _ hjo, k.num (fun i hi ei => hjo (by simp at hi; subst hi; exact ei.symm))
        (fun d hd => (hds d hd).1) (h.pre.fit (h.live_lt j hj'))]
      exact h.arrs j hj'
  · rcases List.mem_cons.mp hj with rfl | hj'
    · exact ho
    · exact h.live_lt j hj'

/-- A step that writes the header word `d := x` alone. -/
theorem KS.slot1 {d x : Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W [] [d] s.mem t.mem)
    (hd : LsOk d) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (e : slot t.mem P.B d = x) :
    KS P σ A live (upd V d x) (d :: ls) t := by
  have hs : SlotOk d := ⟨hd.1, .inr hd.2.1, hd.2.2⟩
  refine h.core k (by simp) (by simpa using hs) sp rd wr (h.arrs_keep k (by simp) (by simpa using hs))
    (fun d' hd' => ?_) h.live_lt (fun d' hd' => ?_)
  · by_cases e' : d' = d
    · subst e'; rw [upd_self]; exact e
    · have hd'' := (List.mem_cons.mp hd').resolve_left e'
      rw [upd_ne _ _ e', k.slot (h.ls_ok d' hd'').1 (fun y hy => by
        simp only [List.mem_singleton] at hy; subst hy
        exact (h.ls_ok d' hd'').sep hs e'), h.sl d' hd'']
  · rcases List.mem_cons.mp hd' with rfl | hd''
    · exact hd
    · exact h.ls_ok d' hd''

/-- `str r, [r8, #d]` of a header word `d`. -/
theorem KS.str {d : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (hd : LsOk d) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd V d (s.gpr r).toNat) (d :: ls) t → Ws t P.B P.Z P.W nArr → Mupd s t
      (s.mem.writeW (off (State.addr P.B) d) (s.gpr r)) → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q :=
  wp_strSlot hw hd.1 fun t m => by
    have kt : Keep P.B P.W [] [d] s.mem t.mem := by
      rw [m.mem]; exact keep_write _ _ (by simp) (by have := hd.1; simp only [hdr] at this; omega)
    exact k t (h.slot1 kt hd m.sp m.rd m.wr (by rw [m.mem, slot_write_self])) (hw.of_mupd m) m

/-- `str r, [r8, #d]`, keeping the Z flag. -/
theorem KS.strz {d : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (hd : LsOk d) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd V d (s.gpr r).toNat) (d :: ls) t → Ws t P.B P.Z P.W nArr → t.z = s.z →
      WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q := by
  have := hw.hdr_le
  refine wp_str_z (by have := hd.1; simp only [hdr] at this; omega) (slot_addr hw (by have := hd.1; omega))
    (hw.write (by have := hd.1; omega)) fun t m z => ?_
  have kt : Keep P.B P.W [] [d] s.mem t.mem := by
    rw [m.mem]; exact keep_write _ _ (by simp) (by have := hd.1; simp only [hdr] at this; omega)
  exact k t (h.slot1 kt hd m.sp m.rd m.wr (by rw [m.mem, slot_write_self])) (hw.of_mupd m) z

/-- `ldr r, [r8, #d]` of a header word the stage holds. -/
theorem KS.ldr {d : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (hd : d ∈ ls) {r : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live V ls t → Ws t P.B P.Z P.W nArr → Upd s t r (BitVec.ofNat 32 (V d)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldr r .r8 d :: rest)) s Q :=
  wp_ldrSlot hw (h.ls_ok d hd).1 fun t u => by
    have e : s.mem.readW (off (State.addr P.B) d) 32 = BitVec.ofNat 32 (V d) := by
      rw [← h.sl d hd]; simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [e] at u
    exact k t (h.of_rest (u.rest (ws := [r]) (by simp)) u.mem)
      (hw.of_upd u (fun x => hr (by simp [x])) (fun x => hr (by simp [x])) (fun x => hr (by simp [x]))) u

end

/-! ## Pieces -/

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem St.mono {A' : State → Nat → Nat} {L' : List Nat} {V' : State → Nat → Nat} {LS' : List Nat} {σ s : State}
    (h : St P E A L V LS σ s) (hl : ∀ j ∈ L', j ∈ L ∧ A σ j = A' σ j) (hls : ∀ d ∈ LS', d ∈ LS ∧ V σ d = V' σ d) :
    St P E A' L' V' LS' σ s :=
  ⟨h.1, h.2.1.mono hl hls, h.2.2⟩

/-- `copy o a`. -/
theorem St.pcopy {o a : Nat} (cert : Cert (copy o a)) (ho : o < nArr) (ha : a ∈ L) (hoa : o ≠ a) :
    VP (St P E A L V LS) (copy o a) (St P E (fun σ => upd (A σ) o (A σ a)) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (copy_ok hw ho (h.live_lt a ha) (by decide) hoa) fun _ ⟨ht, k, v, r, _⟩ =>
      ⟨e, h.write1 k ho (by simp) r.sp r.rd r.wr (by rw [v, h.arrs a ha]) (by simp), ht⟩

/-- `sel o a b sl`: `[b]` if the header word `sl` is 1, `[a]` if it is 0. -/
theorem St.psel {o a b sl : Nat} (cert : Cert (sel o a b sl)) (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS) (bit : ∀ σ, E σ → V σ sl ≤ 1) :
    VP (St P E A L V LS) (sel o a b sl)
      (St P E (fun σ => upd (A σ) o (if V σ sl = 0 then A σ a else A σ b)) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ _ ⟨e, h, hw⟩ => by
    have hs := h.sl sl hsl
    refine WP.mono (sel_ok hw ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob (h.ls_ok sl hsl).1
      (by rw [hs]; exact bit σ e)) fun _ ⟨ht, k, v, r⟩ => ⟨e, h.write1 k ho (by simp) r.sp r.rd r.wr ?_ (by simp), ht⟩
    rw [v, hs, h.arrs a ha, h.arrs b hb]

/-- `bitOf d j`: the header word `d := [j] mod 2`. -/
theorem St.pbitOf {d j : Nat} (cert : Cert (.block (bitOf d j))) (hj : j ∈ L) (hd : LsOk d) :
    VP (St P E A L V LS) (.block (bitOf d j))
      (St P E A L (fun σ => upd (V σ) d (b2n (decide (A σ j % 2 = 1)))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (bitOf d j)]
    refine bitOf_ok hw (h.live_lt j hj) (by decide) hd.1 fun t ht k v r => WP.block_nil ⟨e, ?_, ht⟩
    rw [h.arrs j hj, b2n_mod2] at v
    exact h.slot1 k hd r.sp r.rd r.wr v

end

end VG.Proof.Dsa.Arm.Prime
