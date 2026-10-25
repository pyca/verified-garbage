module

public import VerifiedGarbage.Proof.Rsa.Arm.KcLoads
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentScanCT
public import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.CvFin
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads

/-! # The checks of an RSA key on ARMv7: the entry, the checks of `n` and `e`, and the exit

`entry_ok`: the entry reads the numbers and checks `n` (`Mid`, and Z);
`eCheck_ok`: `e` checked (Z); `Mid.bodyIn`: what the checks start from;
`ret_ok`, `restore_ok`: the mask returned and the registers restored.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg bytes_frame num_of_full num_of_zero top_of_full val32_low2)

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

/-- `n` and `e`. -/
abbrev nV (σ : State) : Nat := bytesV σ (σ.gpr .r0) (fK σ)
abbrev eV (σ : State) : Nat := bytesV σ (σ.gpr .r2) (σ.gpr .r3).toNat

/-- The arrays after the entry. -/
def aEnt (ins : List (Nat × Nat)) (σ : State) : Nat → Nat :=
  upd (loadFn σ ins (upd (fun _ => 0) aE (eV σ))) aN (nV σ)

/-- After the entry, and the check of `e`. -/
structure Mid (nA iS : Nat) (ins : List (Nat × Nat)) (σ s : State) (A : Nat → Nat) : Prop where
  base : FnBase nA iS ins σ s
  ws : WsR s (geo iS σ).B (geo iS σ).Z (geo iS σ).w nArr
  cnt : s.mem.readW (off (State.addr (geo iS σ).B) 16) 32 = BitVec.ofNat 32 (geo iS σ).w
  full : ∀ j < nArr, val32 s.mem (State.addr (geo iS σ).B) (arr (geo iS σ).w j) ((geo iS σ).w + 2) = A j
  r11 : s.gpr .r11 = σ.gpr .r1

theorem Mid.of_rest {σ s t : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) {ws : List Reg} (r : Rest ws s t)
    (m : t.mem = s.mem) (h8 : Reg.r8 ∉ ws) (h11 : Reg.r11 ∉ ws) : Mid nA iS ins σ t A :=
  ⟨h.base.of_rest r m, ⟨h.ws.nowrap, by rw [r.wr]; exact h.ws.writable, h.ws.fits, h.ws.wpos, h.ws.wle,
    (r.gpr _ h8).trans h.ws.r8⟩, m ▸ h.cnt, fun j hj => m ▸ h.full j hj, (r.gpr _ h11).trans h.r11⟩

theorem EntSt.mid {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) : Mid nA iS ins σ s A :=
  ⟨h.base, Ws.toR h.ws, h.cnt, h.full, h.r11⟩

theorem entry_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) :
    WP isa (entry (4 * iS) (ins.map fun p => (4 * p.1, p.2))) σ fun t =>
      Mid nA iS ins σ t (aEnt ins σ) ∧ t.z = Spec.Rsa.modulusValid (nV σ) (fK σ) := by
  have kb := h.kb
  unfold entry
  rw [show ∀ (a b c : Prog isa) (l m : List (Prog isa)), [a, b, c] ++ l ++ m = [a, b] ++ (c :: (l ++ m)) from
    fun _ _ _ _ _ => by simp, wp_seqs_append (by simp) (by simp)]
  refine WP.mono (entryFirst_ok h h4) fun t1 ⟨e1, p4, p6⟩ => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (e1.load_ok (j := aE) (by decide) (src := σ.gpr .r2) (k := (σ.gpr .r3).toNat) h.rdE h.eS h.fE
    (by have := h.e1; omega_arith) h.e2 p4 (by rw [p6]; simp)) fun t2 ⟨e2, _⟩ => ?_
  refine e2.loads_ok ins (fun p hp => hp) (by simp) fun t3 e3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => WP.block_nil ?_
  have e5 := e3.of_rest ((u4.rest (ws := [.r4, .r6]) (by simp)).trans (u5.rest (by simp))) (u5.mem.trans u4.mem)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (e5.load_ok (j := aN) (by decide) (src := σ.gpr .r0) (k := fK σ) h.rdN h.nS h.fN
    (by omega_arith) (Nat.le_refl _) (by rw [u5.other _ (by decide), u4.gpr, e3.r10])
    (by rw [u5.gpr, u4.other _ (by decide), e3.r11]; simp)) fun t6 ⟨e6, r6⟩ => ?_
  have p4' : t6.gpr .r4 = σ.gpr .r0 := by
    rw [r6.gpr _ (by decide), u5.other _ (by decide), u4.gpr, e3.r10]
  have p6' : t6.gpr .r6 = BitVec.ofNat 32 (fK σ) := by
    rw [r6.gpr _ (by decide), u5.gpr, u4.other _ (by decide), e3.r11]; simp
  refine WP.mono (modulusCheck_ok t6 (src := σ.gpr .r0) (k := fK σ) kb.1 kb.2 h.fN
    ⟨_, List.mem_append_left _ (by rw [e6.base.rd]; exact h.rdN), Region.contains_self _ _⟩ p4' p6')
    fun t ⟨z, m, r⟩ => ⟨e6.mid.of_rest r m (by decide) (by decide), ?_⟩
  rw [z, bytes_frame e6.base.frame (by simpa using h.nS) (by omega_arith)]

/-- The bytes of `e`. -/
abbrev eBytes (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr (σ.gpr .r2)) (σ.gpr .r3).toNat

/-- `e` and `e_len` into `r1` and `lr`, for `exponentCheck`. -/
theorem eLoad_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) :
    WP isa (.block [.ldr .r1 .r8 sE, .ldr .lr .r8 sEl]) s fun t => Mid nA iS ins σ t A ∧
      ExponentInput (σ.gpr .r2) (eBytes σ) t := by
  have pre := h.base.pre
  have fits := pre.fits
  have nw := h.ws.nowrap
  have eZ : (geo iS σ).Z = (stackArg σ (iS + 1)).toNat * 8 := rfl
  have eB : (geo iS σ).B.toNat = (stackArg σ iS).toNat := rfl
  have fS := pre.fS
  have hz : 64 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  have rdS : (geo iS σ).B.toNat + 64 ≤ 2 ^ 32 := by omega_arith
  have ldS : ∀ (d : Nat) (u : State), Mid nA iS ins σ u A → d + 4 ≤ 64 →
      State.addr (u.gpr .r8 + BitVec.ofNat 32 d) = off (State.addr (geo iS σ).B) d ∧
      InRegions (u.rd ++ u.wr) (off (State.addr (geo iS σ).B) d) 4 := fun d u hu hd =>
    ⟨by rw [hu.ws.r8]; exact VG.Arm.addr_add (by omega_arith),
      ⟨rS iS σ, List.mem_append_right _ (by rw [hu.base.wr, pre.wr]; simp),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩⟩
  refine wp_ldr (by decide) (ldS sE s h (by decide)).1 (ldS sE s h (by decide)).2 fun s1 u1 => ?_
  have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem (by decide) (by decide)
  refine wp_ldr (by decide) (ldS sEl s1 h1 (by decide)).1 (ldS sEl s1 h1 (by decide)).2
    fun s2 u2 => WP.block_nil ?_
  have h2 := h1.of_rest (u2.rest (ws := [.lr]) (by simp)) u2.mem (by decide) (by decide)
  have e1 : s2.gpr .r1 = σ.gpr .r2 := by
    rw [u2.other _ (by decide), u1.gpr]
    exact BitVec.eq_of_toNat_eq (h.base.saved 9 (by decide))
  have e2 : s2.gpr .lr = σ.gpr .r3 := by
    rw [u2.gpr, u1.mem]
    exact BitVec.eq_of_toNat_eq (h.base.saved 10 (by decide))
  have le := pre.e2
  have kb := pre.kb
  have len : (eBytes σ).length = (σ.gpr .r3).toNat := VG.Proof.Rsa.Arm.CrtValues.bytesAt_length _ _ _
  refine ⟨h2, ⟨by rw [len]; omega_arith, by rw [len]; exact pre.fE,
    by rw [len]; exact ⟨_, List.mem_append_left _ (by rw [h2.base.rd]; exact pre.rdE), Region.contains_self _ _⟩,
    fun i hi => ?_⟩, e1, by rw [len, e2]; simp⟩
  rw [len] at hi
  have := bytes_frame h2.base.frame (a := State.addr (σ.gpr .r2)) (n := (σ.gpr .r3).toNat)
    (by simpa using pre.eS) (by omega_arith)
  simp only [Spec.Rsa.bytesAt] at this ⊢
  have := congrArg (fun l => l[i]?) this
  simpa [hi] using this

/-- `exponentCheck`, from its input. -/
theorem expCheck_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A)
    (hi : ExponentInput (σ.gpr .r2) (eBytes σ) s) :
    WP isa exponentCheck s fun t => Mid nA iS ins σ t A ∧
      t.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV σ)).toNat := by
  have pre := h.base.pre
  have len : (eBytes σ).length = (σ.gpr .r3).toNat := VG.Proof.Rsa.Arm.CrtValues.bytesAt_length _ _ _
  exact WP.mono (exponentCheck_ok s (by rw [len]; exact pre.e1) hi.1.countFit hi.1.sourceFit hi.1.read
    hi.1.bytes hi.2.1 hi.2.2) fun t ⟨v, m, r⟩ => ⟨h.of_rest r m (by decide) (by decide), v⟩

/-- `cmp r7, #1`. -/
theorem eCmp_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV σ)).toNat) :
    WP isa (.block [.cmp .r7 (.imm 1)]) s fun t => Mid nA iS ins σ t A ∧
      t.z = Spec.Rsa.exponentValid (eV σ) :=
  wp_cmp (op2_imm (by decide)) fun t u4 z4 => WP.block_nil ⟨h.of_rest (u4.rest []) u4.mem
    (by simp) (by simp), by rw [z4, h7]; cases Spec.Rsa.exponentValid (eV σ) <;> rfl⟩

/-- `eCheck`: Z if `e` is valid. -/
theorem eCheck_ok {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) :
    WP isa eCheck s fun t => Mid nA iS ins σ t A ∧ t.z = Spec.Rsa.exponentValid (eV σ) := by
  unfold eCheck
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eLoad_ok h) fun s1 ⟨h1, i1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  exact WP.mono (expCheck_ok h1 i1) fun s2 ⟨h2, v2⟩ => eCmp_ok h2 v2

/-- What the checks start from. -/
theorem Mid.bodyIn {σ s : State} {A : Nat → Nat} (h : Mid nA iS ins σ s A) (v : Vals)
    (hv : A = vals v) (hA : ∀ j < nArr, A j < 2 ^ (32 * (geo iS σ).w)) : BodyIn (geo iS σ) v s := by
  have pre := h.base.pre
  have w16 := pre.w16
  have hvj : ∀ j < nArr, A j = vals v j := fun j _ => by rw [hv]
  refine ⟨h.ws.nowrap, h.ws.writable, h.ws.fits, pre.kb, h.ws.r8, by rw [h.r11]; simp, h.cnt, fun j hj => ?_,
    ?_⟩
  · have hj' := List.mem_range.mp hj
    rw [← hvj j hj', ← h.full j hj']
    exact val32_low2 (by rw [h.full j hj']; exact hA j hj')
  · have := h.full aVD (by decide)
    have hz : A aVD = 0 := by rw [hvj _ (by decide)]; rfl
    exact top_of_full (this.trans hz)

/-- `ret`: the mask returned. -/
theorem ret_ok {σ s : State} {c : Bool} (h : FnBase nA iS ins σ s) (h8 : s.gpr .r8 = (geo iS σ).B)
    (hm : slot s.mem (geo iS σ).B sMask = if c then 1 else 0) :
    WP isa (.block ret) s fun t => FnBase nA iS ins σ t ∧ t.gpr .r0 = BitVec.ofNat 32 (if c then 1 else 0) := by
  have pre := h.pre
  have fits := pre.fits
  have fS := pre.fS
  have hz : 160 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  have eZ : (geo iS σ).Z = (stackArg σ (iS + 1)).toNat * 8 := rfl
  have eB : (geo iS σ).B.toNat = (stackArg σ iS).toNat := rfl
  have eM : sMask = 120 := rfl
  refine wp_ldr (by decide) (by rw [h8]; exact VG.Arm.addr_add (by omega_arith))
    ⟨rS iS σ, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    fun t u => WP.block_nil ⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, ?_⟩
  rw [u.gpr]
  apply BitVec.eq_of_toNat_eq
  rw [show (s.mem.readW (off (State.addr (geo iS σ).B) sMask) 32).toNat = slot s.mem (geo iS σ).B sMask from rfl,
    hm]
  cases c <;> rfl

theorem ldrSaved {σ s : State} (h : FnBase nA iS ins σ s) (p12 : s.gpr .r12 = (geo iS σ).B) {i : Nat}
    (hi : i < 11) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (σ.gpr (savedReg i)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr t .r12 (20 + 4 * i) :: rest)) s Q := by
  have pre := h.pre
  have fS := pre.fS
  have fits := pre.fits
  have hz : 64 ≤ (geo iS σ).Z := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_arith) fits
  have eZ : (geo iS σ).Z = (stackArg σ (iS + 1)).toNat * 8 := rfl
  have eB : (geo iS σ).B.toNat = (stackArg σ iS).toNat := rfl
  refine wp_ldr (by omega_arith) (by rw [p12]; exact addr_add (by omega_arith))
    ⟨rS iS σ, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    fun s' u => k s' ?_
  have e : s.mem.readW (off (State.addr (geo iS σ).B) (20 + 4 * i)) 32 = σ.gpr (savedReg i) :=
    BitVec.eq_of_toNat_eq (h.saved i hi)
  exact ⟨by rw [u.gpr]; exact e, u.other, u.mem, u.rd, u.wr, u.sp⟩

theorem restore_ok {σ s : State} (h : FnBase nA iS ins σ s) (h4 : 4 * iS < 4096) :
    WP isa (.block (restore (4 * iS))) s fun t => (∀ r ∈ preserved, t.gpr r = σ.gpr r) ∧ t.sp = σ.sp ∧
      t.mem = s.mem ∧ t.gpr .r0 = s.gpr .r0 := by
  have pre := h.pre
  refine h.ldrSp (i := iS) (by have := pre.hS; omega_arith) h4 fun s1 d1 u1 => ?_
  have p12 : s1.gpr .r12 = (geo iS σ).B := u1.gpr
  refine ldrSaved d1 p12 (i := 0) (by decide) fun s2 u2 => ?_
  have d2 := d1.of_rest (u2.rest (ws := [.r4]) (by simp)) u2.mem
  refine ldrSaved d2 (by rw [u2.other _ (by decide), p12]) (i := 1) (by decide) fun s3 u3 => ?_
  have d3 := d2.of_rest (u3.rest (ws := [.r5]) (by simp)) u3.mem
  refine ldrSaved d3 (by rw [u3.other _ (by decide), u2.other _ (by decide), p12]) (i := 2) (by decide)
    fun s4 u4 => ?_
  have d4 := d3.of_rest (u4.rest (ws := [.r6]) (by simp)) u4.mem
  have q4 : s4.gpr .r12 = (geo iS σ).B := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p12]
  refine ldrSaved d4 q4 (i := 3) (by decide) fun s5 u5 => ?_
  have d5 := d4.of_rest (u5.rest (ws := [.r7]) (by simp)) u5.mem
  refine ldrSaved d5 (by rw [u5.other _ (by decide), q4]) (i := 4) (by decide) fun s6 u6 => ?_
  have d6 := d5.of_rest (u6.rest (ws := [.r8]) (by simp)) u6.mem
  have q6 : s6.gpr .r12 = (geo iS σ).B := by rw [u6.other _ (by decide), u5.other _ (by decide), q4]
  refine ldrSaved d6 q6 (i := 5) (by decide) fun s7 u7 => ?_
  have d7 := d6.of_rest (u7.rest (ws := [.r9]) (by simp)) u7.mem
  refine ldrSaved d7 (by rw [u7.other _ (by decide), q6]) (i := 6) (by decide) fun s8 u8 => ?_
  have d8 := d7.of_rest (u8.rest (ws := [.r10]) (by simp)) u8.mem
  have q8 : s8.gpr .r12 = (geo iS σ).B := by rw [u8.other _ (by decide), u7.other _ (by decide), q6]
  refine ldrSaved d8 q8 (i := 7) (by decide) fun s9 u9 => ?_
  have d9 := d8.of_rest (u9.rest (ws := [.r11]) (by simp)) u9.mem
  refine ldrSaved d9 (by rw [u9.other _ (by decide), q8]) (i := 8) (by decide) fun t u10 => WP.block_nil ?_
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.other _ (by decide), u5.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
        u6.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr]; rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr]; rfl
    · rw [u10.other _ (by decide), u9.gpr]; rfl
    · rw [u10.gpr]; rfl
  · rw [u10.sp, d9.sp]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide)]

/-- The function's result, from the checks' mask `c` (with `P c`). -/
def FnPost (σ u : State) (P : Bool → Prop) : Prop :=
  abiPreserved σ u ∧ ∃ c : Bool,
    (Spec.Rsa.modulusValid (nV σ) (fK σ) = true → Spec.Rsa.exponentValid (eV σ) = true → P c) ∧
    u.gpr .r0 = BitVec.ofNat 32
      (if Spec.Rsa.modulusValid (nV σ) (fK σ) && Spec.Rsa.exponentValid (eV σ) && c then 1 else 0)

/-- A function: the entry, the checks `body`, the exit. -/
theorem fn_ok {σ : State} (h : FnPre nA iS ins σ) (h4 : 4 * iS < 4096) {body : Prog isa} {v : Vals}
    {P : Bool → Prop} (hv : aEnt ins σ = vals v)
    (hA : ∀ j < nArr, aEnt ins σ j < 2 ^ (32 * (geo iS σ).w))
    (hbody : ∀ s, BodyIn (geo iS σ) v s →
      WP isa body s fun t => ∃ A live c, Stg (geo iS σ) s A live c t ∧ P c) :
    WP isa (fn (4 * iS) (ins.map fun p => (4 * p.1, p.2)) body) σ fun u => FnPost σ u P := by
  unfold fn
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (entry_ok h h4) fun s1 ⟨m1, z1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  -- What the three ways out leave for `restore`.
  have exit : ∀ (u : State) (c : Bool), FnBase nA iS ins σ u → (Spec.Rsa.modulusValid (nV σ) (fK σ) = true →
      Spec.Rsa.exponentValid (eV σ) = true → P c) →
      u.gpr .r0 = BitVec.ofNat 32
        (if Spec.Rsa.modulusValid (nV σ) (fK σ) && Spec.Rsa.exponentValid (eV σ) && c then 1 else 0) →
      WP isa (seqs [.block (restore (4 * iS))]) u fun u' => FnPost σ u' P := fun u c hu hp hr =>
    WP.mono (restore_ok hu h4) fun u' ⟨pres, sp, _, r0⟩ => ⟨⟨pres, sp⟩, c, hp, r0.trans hr⟩
  refine WP.ite s1.z rfl (fun hn => ?_) (fun hn => ?_)
  · rw [WP.seq_iff]
    refine WP.mono (eCheck_ok m1) fun s2 ⟨m2, z2⟩ => ?_
    refine WP.ite s2.z rfl (fun he => ?_) (fun he => ?_)
    · rw [WP.seq_iff]
      have bi := m2.bodyIn v hv hA
      refine WP.mono (hbody s2 bi) fun t ⟨A, live, c, ht, hP⟩ => ?_
      have bt : FnBase nA iS ins σ t := m2.base.keep ht.keep (fun j hj => List.mem_range.mp hj) (by decide)
        (by decide) ht.rest.sp ht.rest.rd ht.rest.wr
      refine WP.mono (ret_ok bt ht.ws.r8 ht.mask) fun u ⟨bu, ru⟩ => exit u c bu (fun _ _ => hP) ?_
      rw [ru, ← z1, ← z2, hn, he]
      rfl
    · refine wp_mov (op2_imm (by decide)) fun u up => WP.block_nil ?_
      refine exit u false (m2.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem) (fun _ e => ?_) ?_
      · rw [← z2, he] at e; cases e
      · rw [up.gpr, ← z2, he]; simp
  · refine wp_mov (op2_imm (by decide)) fun u up => WP.block_nil ?_
    refine exit u false (m1.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem) (fun e _ => ?_) ?_
    · rw [← z1, hn] at e; cases e
    · rw [up.gpr, ← z1, hn]; simp

end

end VG.Proof.Rsa.Arm.KeyCheck
