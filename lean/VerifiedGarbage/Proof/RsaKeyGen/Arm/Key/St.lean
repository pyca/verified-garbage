module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Base
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Words
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
public import VerifiedGarbage.Proof.Rsa.Arm.RvSk
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Rsa.Arm.RvCand3
import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: the operations as pieces

`St P E A L V LS`: a stage (`KS`) with the working space's registers (`Ws`),
the values `A σ` and `V σ` given by the state `σ` the body starts from. The
operations of the key working space as pieces (`VP`): correct from any such
stage, and leaking the same in two runs at it, by the taint analysis of each
piece (`Cert`) with `r7`–`r9` public. Flags are `b2n` of booleans.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)
open VG.Proof.Rsa (b2n)

set_option hygiene false in
/-- Case split on `hj : j ∈ l` for a literal list `l`. -/
macro "mem_cases" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; repeat' rcases hj with rfl | hj))

set_option hygiene false in
/-- `j ∈ l'` from `hj : j ∈ l` for literal lists. -/
macro "mem_sub" : tactic => `(tactic| (revert hj; revert j; decide))

/-- The working space's registers. -/
abbrev kRegs : List Reg := [.r7, .r8, .r9]

/-- A stage with the working space's registers. -/
abbrev St (P : KP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (V σ) LS s ∧ Ws s P.B P.Z P.W nArr

/-- A piece the taint analysis checks with the working space's registers public. -/
theorem VP.kv {F G : State → State → Prop} {c : Prog isa} {P : KP} (cert : Cert c)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z P.W nArr) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    have w₁ := hws _ _ h₁; have w₂ := hws _ _ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]) wp

theorem b2n_xor (x : Bool) : (BitVec.ofNat 32 (b2n x) ^^^ (1 : BitVec 32)).toNat = b2n (!x) := by
  cases x <;> decide

theorem b2n_and (x y : Bool) :
    (BitVec.ofNat 32 (b2n x) &&& BitVec.ofNat 32 (b2n y)).toNat = b2n (x && y) := by
  cases x <;> cases y <;> decide

theorem b2n_or (x y : Bool) :
    (BitVec.ofNat 32 (b2n x) ||| BitVec.ofNat 32 (b2n y)).toNat = b2n (x || y) := by
  cases x <;> cases y <;> decide

theorem b2n_mod2 (n : Nat) : n % 2 = b2n (decide (n % 2 = 1)) := by
  unfold b2n; split <;> simp_all <;> omega

theorem b2n_eq_one (x : Bool) : (b2n x = 1) = (x = true) := by cases x <;> decide

theorem b2n_lt (x : Bool) : b2n x < 2 ^ 32 := by cases x <;> decide

section
variable {P : KP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

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

/-- A number of the stage is below `2^(32 W)`. -/
theorem KS.lt (h : KS P σ A live V ls s) {j : Nat} (hj : j ∈ live) : A j < 2 ^ (32 * P.W) := by
  rw [← h.arrs j hj]; exact val32_lt _ _ _ _

end

/-! ## Pieces -/

section
variable {P : KP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem St.mono {A' : State → Nat → Nat} {L' : List Nat} {V' : State → Nat → Nat} {LS' : List Nat} {σ s : State}
    (h : St P E A L V LS σ s) (hl : ∀ j ∈ L', j ∈ L ∧ A σ j = A' σ j) (hls : ∀ d ∈ LS', d ∈ LS ∧ V σ d = V' σ d) :
    St P E A' L' V' LS' σ s :=
  ⟨h.1, h.2.1.mono hl hls, h.2.2⟩

/-- Fewer arrays and header words. -/
theorem St.sub {L' LS' : List Nat} {σ s : State} (h : St P E A L V LS σ s) (hl : ∀ j ∈ L', j ∈ L)
    (hls : ∀ d ∈ LS', d ∈ LS) : St P E A L' V LS' σ s :=
  h.mono (fun j hj => ⟨hl j hj, rfl⟩) fun d hd => ⟨hls d hd, rfl⟩

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

/-- `ltS d a b`: the header word `d := [a] < [b]`, and `[aTmp] := [a] − [b]`. -/
theorem St.pltS {d a b : Nat} (cert : Cert (seqs (ltS d a b))) (ha : a ∈ L) (hb : b ∈ L) (hTa : aTmp ≠ a)
    (hTb : aTmp ≠ b) (hd : LsOk d) :
    VP (St P E A L V LS) (seqs (ltS d a b))
      (St P E (fun σ => upd (A σ) aTmp (sub32 P.W (A σ a) (A σ b))) (aTmp :: L)
        (fun σ => upd (V σ) d (b2n (decide (A σ a < A σ b)))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    simp only [ltS, seqs]
    rw [WP.seq_iff]
    refine WP.mono (sub3_ok hw (by decide) (h.live_lt a ha) (h.live_lt b hb) (by decide) hTa hTb)
      fun t ⟨ht, k, v, bo, r⟩ => ?_
    obtain ⟨e1, e2⟩ := sub32_of (val32_lt _ _ _ _) (val32_lt _ _ _ _) v bo
    have ea : val32 s.mem (State.addr P.B) (arr P.W a) P.W = A σ a := h.arrs a ha
    have eb : val32 s.mem (State.addr P.B) (arr P.W b) P.W = A σ b := h.arrs b hb
    simp only [num, ea, eb] at e1 e2
    have h1 := h.write1 k (by decide) (by simp) r.sp r.rd r.wr e1 (by simp)
    exact h1.str ht hd fun u hu hwu _ => WP.block_nil ⟨e, by rw [e2] at hu; exact hu, hwu⟩

/-- `eqS d a b aTmp`: the header word `d := [a] = [b]`. -/
theorem St.peqS {d a b : Nat} (cert : Cert (eqS d a b aTmp)) (ha : a ∈ L) (hb : b ∈ L) (hd : LsOk d)
    (hT : aTmp ∉ L) (hls : sT ∉ LS) (hdT : d ≠ sT) :
    VP (St P E A L V LS) (eqS d a b aTmp)
      (St P E A L (fun σ => upd (V σ) d (b2n (decide (A σ a = A σ b)))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    have hTa : aTmp ≠ a := fun x => hT (x ▸ ha)
    have hTb : aTmp ≠ b := fun x => hT (x ▸ hb)
    refine WP.mono (eqS_ok hw (t := aTmp) (by decide) (h.live_lt a ha) (h.live_lt b hb) (by decide)
      hTa hTb hd.1) fun t ⟨ht, k, v, r⟩ => ⟨e, ?_, ht⟩
    have hs : SlotOk d := ⟨hd.1, .inr hd.2.1, hd.2.2⟩
    have hds : ∀ x ∈ [sT, d], SlotOk x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · decide
      · rw [List.mem_singleton.mp hx]; exact hs
    refine h.core k (by decide) hds r.sp r.rd r.wr
      (h.arrs_keep k (fun j hj e => by simp at e; exact hT (e ▸ hj)) hds) (fun x hx => ?_) h.live_lt
      (fun x hx => ?_)
    · by_cases e' : x = d
      · subst e'; dsimp only; rw [upd_self, v, h.arrs a ha, h.arrs b hb]; unfold b2n; simp
      · have hx' := (List.mem_cons.mp hx).resolve_left e'
        dsimp only
        rw [upd_ne _ _ e', k.slot (h.ls_ok x hx').1 (fun y hy => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact (h.ls_ok x hx').sep (by decide) (fun x' => hls (x' ▸ hx'))
          · exact (h.ls_ok x hx').sep hs e'), h.sl x hx']
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact hd
      · exact h.ls_ok x hx'

/-- `bitOf d j`: the header word `d := [j] mod 2`. -/
theorem St.pbitOf {d j : Nat} (cert : Cert (.block (bitOf d j))) (hj : j ∈ L) (hd : LsOk d) :
    VP (St P E A L V LS) (.block (bitOf d j))
      (St P E A L (fun σ => upd (V σ) d (b2n (decide (A σ j % 2 = 1)))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (bitOf d j)]
    refine bitOf_ok hw (h.live_lt j hj) (by decide) hd.1 fun t ht k v r => WP.block_nil ⟨e, ?_, ht⟩
    rw [h.arrs j hj, b2n_mod2] at v
    exact h.slot1 k hd r.sp r.rd r.wr v

/-- `notS d a`: the header word `d :=` not `a`. -/
theorem St.pnotS {d a : Nat} {X : State → Bool} (cert : Cert (.block (notS d a))) (ha : a ∈ LS) (hd : LsOk d)
    (hX : ∀ σ, E σ → V σ a = b2n (X σ)) :
    VP (St P E A L V LS) (.block (notS d a)) (St P E A L (fun σ => upd (V σ) d (b2n (!X σ))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold notS
    refine h.ldr hw ha (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
    have hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
    refine h2.str hw2 hd fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    rwa [u2.gpr, dpVal, u1.gpr, hX σ e, b2n_xor] at ht

/-- `andS d a b`: the header word `d := a ∧ b`. -/
theorem St.pandS {d a b : Nat} {X Y : State → Bool} (cert : Cert (.block (andS d a b))) (ha : a ∈ LS)
    (hb : b ∈ LS) (hd : LsOk d) (hX : ∀ σ, E σ → V σ a = b2n (X σ)) (hY : ∀ σ, E σ → V σ b = b2n (Y σ)) :
    VP (St P E A L V LS) (.block (andS d a b))
      (St P E A L (fun σ => upd (V σ) d (b2n (X σ && Y σ))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold andS
    refine h.ldr hw ha (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine h1.ldr hw1 hb (r := .r2) (by decide) fun s2 h2 hw2 u2 => ?_
    refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
    have h3 := h2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
    have hw3 := hw2.of_upd u3 (by decide) (by decide) (by decide)
    refine h3.str hw3 hd fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    rwa [u3.gpr, dpVal, u2.gpr, u2.other _ (by decide), u1.gpr, hX σ e, hY σ e, b2n_and] at ht

/-- `andNotS d a b`: the header word `d := ¬a ∧ b`. -/
theorem St.pandNotS {d a b : Nat} {X Y : State → Bool} (cert : Cert (.block (andNotS d a b))) (ha : a ∈ LS)
    (hb : b ∈ LS) (hd : LsOk d) (hX : ∀ σ, E σ → V σ a = b2n (X σ)) (hY : ∀ σ, E σ → V σ b = b2n (Y σ)) :
    VP (St P E A L V LS) (.block (andNotS d a b))
      (St P E A L (fun σ => upd (V σ) d (b2n (!X σ && Y σ))) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold andNotS
    refine h.ldr hw ha (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
    have hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
    refine h2.ldr hw2 hb (r := .r2) (by decide) fun s3 h3 hw3 u3 => ?_
    refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
    have h4 := h3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem
    have hw4 := hw3.of_upd u4 (by decide) (by decide) (by decide)
    refine h4.str hw4 hd fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    have x1 : s3.gpr .r1 = BitVec.ofNat 32 (b2n (!X σ)) := by
      rw [u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hX σ e]
      apply BitVec.eq_of_toNat_eq; rw [b2n_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (b2n_lt _)]
    rwa [u4.gpr, dpVal, u3.gpr, x1, hY σ e, b2n_and] at ht

/-- `isOne d`: Z iff the header word `d` holds 1. -/
theorem St.pisOne {d : Nat} (cert : Cert (.block (isOne d))) (hd : d ∈ LS) (bit : ∀ σ, E σ → V σ d ≤ 1) :
    VP (St P E A L V LS) (.block (isOne d)) fun σ s => St P E A L V LS σ s ∧ s.z = decide (V σ d = 1) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold isOne
    refine h.ldr hw hd (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨⟨e, h1.of_rest (f.rest []) f.mem, hw1.of (by rw [f.gpr]) (by rw [f.gpr]) (by rw [f.gpr]) f.wr⟩, ?_⟩
    rw [z, u1.gpr]
    have := bit σ e
    rcases (by omega : V σ d = 0 ∨ V σ d = 1) with h0 | h0 <;> rw [h0] <;> decide

end

end VG.Proof.RsaKeyGen.Arm.Key
