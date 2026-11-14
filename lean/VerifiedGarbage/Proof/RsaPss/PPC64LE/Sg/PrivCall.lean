module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Spec
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `RsaPss.PPC64LE.Sg.PrivArgs`, which only this module used -/

section

/-!
# RSASSA-PSS signing on PPC64LE: the private operation's arguments

Untrusted: everything here is checked by Lean. In the frame of `privBytes`
bytes below ours (`pb`), `privArgs` writes `vg_rsa_private_checked`'s twelve
stack arguments to its Parameter Save Area (`psa`: `p`, `p_len`, our stack
arguments 0 to 7, the rest of `scratch` and its length in words) and sets its
registers: `out`, `n`, `e` and `EM` (`AtPriv`), as RSAES-OAEP decryption does.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx hiRegs kR fb fr stackArgAddr_fb saved_offs
  allocated_sp allocated_rd allocated_wr allocated_gpr allocated_mem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_std wp_mov wp_li wp_add wp_addi wp_subi wp_addSp wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem privBytes_rng (pc : Bool) : 192 ≤ privBytes pc ∧ privBytes pc ≤ 208 := by
  cases pc <;> decide

theorem privBytes_mod (pc : Bool) : privBytes pc % 16 = 0 := by cases pc <;> decide

theorem pbd {pc : Bool} {d : Nat} (h : d ≤ 192) : d ≤ privBytes pc := Nat.le_trans h (privBytes_rng pc).1

/-- The base of the private operation's frame. -/
abbrev pb (pc : Bool) (s : State) : Addr := fb s - BitVec.ofNat 64 (privBytes pc)

/-- Its stack argument `i`, as `privArgs` writes it. -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .r9
  | 1 => s.gpr .r10
  | 10 => Ss s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)
  | 12 => stackArg s 16
  | 13 => stackArg s 17
  | i + 2 => stackArg s i

/-- The call's stack arguments: 12, or with `pc` 14. -/
abbrev nP (pc : Bool) : Nat := if pc then 14 else 12

theorem pb_eq (s : State) : pb pc s = s.sp - BitVec.ofNat 64 (frameBytes + privBytes pc) := by
  rw [pb, fb, BitVec.sub_sub, BitVec.ofNat_add]

theorem pb_base (s : State) :
    pb pc s = (s.sp - BitVec.ofNat 64 (stackBytes pc)) + BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes := by
  rw [pb, fb, ← Offset.sub_add_eq, ← BitVec.ofNat_add, ← Offset.sub_sub_eq,
    Offset.ofNat_sub_ofNat (by have := stackBytes_ge pc; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [this])]
  rw [show stackBytes pc - Impl.Rsa.PPC64LE.Priv.frameBytes = frameBytes + privBytes pc by unfold stackBytes; omega_using []]

/-- The region of `pb pc s + d` within the stack the function uses. -/
theorem pb_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes + privBytes pc) :
    Region.Sub ⟨pb pc s + BitVec.ofNat 64 d, n⟩ (kS pc s) := by
  rw [pb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes; omega_using [h])

/-- In the private operation's frame, at the call, with `em` at `scratch`. -/
structure AtPriv (pc : Bool) (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = pb pc s
  rd : t.rd = s.rd
  wr : t.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr
  mem : Frame [kS pc s, SC Ss s] s.mem t.mem
  em : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r5
  r6 : t.gpr .r6 = s.gpr .r6
  r7 : t.gpr .r7 = s.gpr .r7
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = off (Ss s) oEm
  r10 : t.gpr .r10 = s.gpr .r6
  psa : ∀ i < nP pc, t.mem.readW (pb pc s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i

/-- The state of the copies of our stack arguments: `n` of them done. -/
structure Cp (pc : Bool) (s t₀ : State) (n : Nat) (t : State) : Prop where
  k : Keep [.r0] t₀ t
  mem : Frame [⟨pb pc s + BitVec.ofNat 64 112, 64⟩] t₀.mem t.mem
  got : ∀ j < n, t.mem.readW (pb pc s + BitVec.ofNat 64 (112 + 8 * j)) 64 = stackArg s j

theorem privArgs_eq : privArgs pc = (([.addSp .r12 0, .store .d .r17 .r12 96, .store .d .r18 .r12 104] : List Instr) ++
    ((List.range 8).flatMap fun j => [.load .d .r0 .r12 (argP pc j), .store .d .r0 .r12 (112 + 8 * j)])) ++
    (([.li .r0 oRsa, .add .r0 .r14 .r0, .store .d .r0 .r12 176, .load .d .r11 .r12 (argP pc 13),
      .subi .r11 .r11 1024, .store .d .r11 .r12 184] : List Instr) ++ (preArgs pc ++
    ([Impl.AesGcm.PPC64LE.mov .r3 .r16,
      Impl.AesGcm.PPC64LE.mov .r4 .r15, Impl.AesGcm.PPC64LE.mov .r5 .r20, Impl.AesGcm.PPC64LE.mov .r6 .r15,
      Impl.AesGcm.PPC64LE.mov .r7 .r21, Impl.AesGcm.PPC64LE.mov .r8 .r22, .addi .r9 .r14 oEm,
      Impl.AesGcm.PPC64LE.mov .r10 .r15] : List Instr))) := by
  simp only [privArgs, List.append_assoc, List.cons_append, List.nil_append]

theorem sub_ofNat {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega_using [h]), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega_using [])]; omega_using [h]

/-- The private operation's frame. -/
abbrev PB (pc : Bool) (s : State) : Region := ⟨pb pc s, privBytes pc⟩

theorem pb_in (s : State) {d : Nat} (h : d + 8 ≤ privBytes pc) : (PB pc s).Contains (pb pc s + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ h (by have := privBytes_rng pc; omega_using [h, this])

theorem psa_in {s : State} {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ privBytes pc) :
    InRegions (⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr) (pb pc s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by have := privBytes_rng pc; omega_using [h₂])
    (by have := privBytes_rng pc; omega_using [this])⟩

section
variable {D : Nat} {s : State} (P : PreS pc D s)
include P

omit P in
theorem PB_sub : Region.Sub (PB pc s) (kS pc s) := by
  have := pb_sub (pc := pc) s (d := 0) (n := privBytes pc) (by omega_using []); rwa [BitVec.add_zero] at this

/-- A load of our stack argument `j` through `b`, which holds `fb s - o`. -/
theorem wp_argS {t : State} {r b : Reg} {j o : Nat} {is : List Instr} {Q : State → Prop}
    (ha : (aR pc s).Contains (stackArgAddr s j) 8)
    (hb : t.gpr b = fb s - BitVec.ofNat 64 o) (hrd : t.rd = s.rd) (hm : Frame [kS pc s, SC Ss s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : o + arg j < 2 ^ 15 ∧ (o + arg j) % 4 = 0 := by decide) (hb0 : b ≠ .r0 := by decide) :
    WP isa (.block (.load .d r b (o + arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by
    rw [hb, stackArgAddr_fb, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]) ?_
    (fun t' o' e => k t' o' ?_) hb0 ho
  · rw [hrd, P.hrd]; exact ⟨aR pc s, by simp, ha⟩
  · rw [e, stackArg, hm.readW ha (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.ka.symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

/-- The copies of our stack arguments 0 to `n - 1`. -/
theorem copies_ok {t₀ : State} (h12 : t₀.gpr .r12 = pb pc s) (hrd : t₀.rd = s.rd)
    (hwr : t₀.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr) (hm : Frame [kS pc s, SC Ss s] s.mem t₀.mem) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun j =>
      [.load .d .r0 .r12 (argP pc j), .store .d .r0 .r12 (112 + 8 * j)])) t₀ (Cp pc s t₀ n)
  | 0, _ => wp_nil ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (copies_ok h12 hrd hwr hm n (by omega_using [hn])) fun t ⟨k, fm, got⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hmt : Frame [kS pc s, SC Ss s] s.mem t.mem := hm.trans (fm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kS pc s, List.mem_cons_self .., pb_sub s (by have := privBytes_rng pc; unfold frameBytes; omega_using [])⟩)
    have hb : t.gpr .r12 = fb s - BitVec.ofNat 64 (privBytes pc) := by rw [k.get .r12, h12]
    refine wp_argS P (j := n) (o := privBytes pc) (in_aR (by omega_using [hn])) hb (k.rd.trans hrd) hmt (fun t₁ o₁ e₁ => ?_)
      ⟨by have := privBytes_rng pc; unfold arg frameBytes; omega_using [hn, this],
        by have := privBytes_mod pc; unfold arg frameBytes; omega_using [this]⟩
    have hw : InRegions t₁.wr (pb pc s + BitVec.ofNat 64 (112 + 8 * n)) 8 := by
      rw [o₁.wr, k.wr, hwr]; exact psa_in (by omega_using []) (by have := privBytes_rng pc; omega_using [hn, this])
    refine wp_std (a := pb pc s + BitVec.ofNat 64 (112 + 8 * n)) (by rw [o₁.get .r12, hb]) hw (fun t₂ m₂ => wp_nil ?_)
      (by decide) ⟨by omega_using [hn], by omega_using []⟩
    have k₂ : Keep [.r0] t₀ t₂ := (k.trans (o₁.keep.trans m₂.keep)).mono
    refine ⟨k₂, ?_, fun j hj => ?_⟩
    · rw [m₂.mem, o₁.mem]
      exact fm.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using []))
    · rw [m₂.mem, o₁.mem]
      by_cases hj' : j < n
      · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hj'])) (by omega_using [hn, hj]) (by omega_using [hn])) (by decide), got j hj']
      · rw [show j = n by omega_using [hj, hj'], Mem.readW_writeW_self64, e₁]

/-- With `pc`, our stack arguments 16 and 17, `pre` and `pre_len`, to the
call's 12 and 13. -/
theorem preArgs_ok {u : State} (h12 : u.gpr .r12 = pb pc s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr)
    (hm : Frame [kS pc s, SC Ss s] s.mem u.mem) :
    WP isa (.block (preArgs pc)) u fun u' => Keep [.r0] u u' ∧
      Frame [⟨pb pc s + BitVec.ofNat 64 192, privBytes pc - 192⟩] u.mem u'.mem ∧
      (pc = true → u'.mem.readW (pb pc s + BitVec.ofNat 64 192) 64 = stackArg s 16 ∧
        u'.mem.readW (pb pc s + BitVec.ofNat 64 200) 64 = stackArg s 17) := by
  cases pc with
  | false => exact wp_nil ⟨Keep.refl _ _, Frame.refl _ _, fun h => nomatch h⟩
  | true =>
    have hb : u.gpr .r12 = fb s - BitVec.ofNat 64 (privBytes true) := h12
    have in18 : ∀ {j : Nat}, j < 18 → (aR true s).Contains (stackArgAddr s j) 8 := fun hj => by
      rw [VG.Proof.RsaOaep.PPC64LE.stackArgAddr_eq s _]
      exact Offset.contains_base _ (by simp only [↓reduceIte]; omega_using [hj]) (by omega_using [hj])
    refine wp_argS P (j := 16) (o := privBytes true) (in18 (by decide)) hb hrd hm (fun u₁ o₁ e₁ => ?_)
      ⟨by decide, by decide⟩
    refine wp_std (a := pb true s + BitVec.ofNat 64 192) (by rw [o₁.get .r12, h12])
      (by rw [o₁.wr, hwr]; exact psa_in (by decide) (by decide)) fun u₂ m₂ => ?_
    have f₂ : Frame [⟨pb true s + BitVec.ofNat 64 192, privBytes true - 192⟩] u.mem u₂.mem := by
      rw [m₂.mem, o₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by simp only [privBytes, ↓reduceIte]; omega_using []) (by decide))
    have hm₂ : Frame [kS true s, SC Ss s] s.mem u₂.mem := hm.trans (f₂.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kS true s, List.mem_cons_self .., pb_sub s (by decide)⟩)
    refine wp_argS P (j := 17) (o := privBytes true) (in18 (by decide)) (by rw [m₂.gpr, o₁.get .r12, hb])
      (by rw [m₂.rd, o₁.rd, hrd]) hm₂ (fun u₃ o₃ e₃ => ?_) ⟨by decide, by decide⟩
    refine wp_std (a := pb true s + BitVec.ofNat 64 200) (by rw [o₃.get .r12, m₂.gpr, o₁.get .r12, h12])
      (by rw [o₃.wr, m₂.wr, o₁.wr, hwr]; exact psa_in (by decide) (by decide)) fun u₄ m₄ => wp_nil ?_
    refine ⟨(o₁.keep.trans (m₂.keep.trans (o₃.keep.trans m₄.keep))).mono, ?_, fun _ => ⟨?_, ?_⟩⟩
    · rw [m₄.mem, o₃.mem]
      exact f₂.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by simp only [privBytes, ↓reduceIte]; omega_using []) (by decide))
    · rw [m₄.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), o₃.mem,
        m₂.mem, Mem.readW_writeW_self64, e₁]
    · rw [m₄.mem, Mem.readW_writeW_self64, e₃]

theorem privArgs_ok {t : State} (h : Base Ss vS s t) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em) :
    WP isa (.block (privArgs pc)) (allocated (privBytes pc) t) (AtPriv pc s em) := by
  have hsp : t.sp = fb s := h.sv.sp
  have usp : (allocated (privBytes pc) t).sp = pb pc s := by rw [allocated_sp, hsp]
  have uwr : (allocated (privBytes pc) t).wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr := by
    rw [allocated_wr, h.sv.wr, frameR, hsp]; rfl
  have urd : (allocated (privBytes pc) t).rd = s.rd := by rw [allocated_rd, h.rd]
  have um : Frame [PB pc s] t.mem (allocated (privBytes pc) t).mem := by
    rw [allocated_mem]
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    rw [hsp, show fb s - BitVec.ofNat 64 (privBytes pc) = pb pc s + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]
    exact pb_in s (pbd (by decide))
  have ug : (allocated (privBytes pc) t).gpr = t.gpr := rfl
  have hmS : ∀ {x : State}, Frame [PB pc s] t.mem x.mem → Frame [kS pc s, SC Ss s] s.mem x.mem := fun hx =>
    (h.mem.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨kS pc s, List.mem_cons_self .., kR_sub⟩
      · exact ⟨SC Ss s, by simp, fun _ h => h⟩).trans
      (hx.sub fun r hr => ⟨kS pc s, List.mem_cons_self .., by rw [List.mem_singleton.mp hr]; exact PB_sub⟩)
  rw [privArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [usp, BitVec.add_zero] at e₁
  refine wp_std (a := pb pc s + BitVec.ofNat 64 96) (by rw [e₁]) (by rw [o₁.wr, uwr]; exact psa_in (by decide) (pbd (by decide)))
    fun u₂ m₂ => ?_
  refine wp_std (a := pb pc s + BitVec.ofNat 64 104) (by rw [m₂.gpr, e₁])
    (by rw [m₂.wr, o₁.wr, uwr]; exact psa_in (by decide) (pbd (by decide))) fun u₃ m₃ => wp_nil ?_
  have k₃ : Keep [.r12] (allocated (privBytes pc) t) u₃ := (o₁.keep.trans (m₂.keep.trans m₃.keep)).mono
  have f₃ : Frame [PB pc s] t.mem u₃.mem := by
    rw [m₃.mem, m₂.mem, o₁.mem]
    exact (um.writeW (List.mem_singleton_self _) _ (pb_in s (pbd (by decide)))).writeW (List.mem_singleton_self _) _
      (pb_in s (pbd (by decide)))
  have r₃₉₆ : u₃.mem.readW (pb pc s + BitVec.ofNat 64 96) 64 = s.gpr .r9 := by
    rw [m₃.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₂.mem,
      Mem.readW_writeW_self64, o₁.get .r17, ug, Base.r17 h]
  have r₃₁₀₄ : u₃.mem.readW (pb pc s + BitVec.ofNat 64 104) 64 = s.gpr .r10 := by
    rw [m₃.mem, Mem.readW_writeW_self64, m₂.gpr, o₁.get .r18, ug, Base.r18 h]
  have g₃ : u₃.gpr .r12 = pb pc s := by rw [m₃.gpr, m₂.gpr, e₁]
  refine WP.mono (copies_ok P (t₀ := u₃) g₃ (by rw [k₃.rd, urd]) (by rw [k₃.wr, uwr]) (hmS f₃) 8 (Nat.le_refl 8))
    fun u₄ ⟨k₄, f₄, got⟩ => ?_
  have g₄ : u₄.gpr .r12 = pb pc s := by rw [k₄.get .r12, g₃]
  have w₄ : u₄.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr := by rw [k₄.wr, k₃.wr, uwr]
  have f₄' : Frame [PB pc s] t.mem u₄.mem := f₃.trans (f₄.sub fun r hr => ⟨PB pc s, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (pbd (by decide))⟩)
  refine wp_li (by decide) fun u₅ o₅ e₅ => wp_add fun u₆ o₆ e₆ => ?_
  have g₆ : u₆.gpr .r12 = pb pc s := by rw [o₆.get .r12, o₅.get .r12, g₄]
  refine wp_std (a := pb pc s + BitVec.ofNat 64 176) (by rw [g₆]) (by rw [o₆.wr, o₅.wr, w₄]; exact psa_in (by decide) (pbd (by decide)))
    fun u₇ m₇ => ?_
  have f₇ : Frame [PB pc s] t.mem u₇.mem := by
    rw [m₇.mem, o₆.mem, o₅.mem]; exact f₄'.writeW (List.mem_singleton_self _) _ (pb_in s (pbd (by decide)))
  have rd₇ : u₇.rd = s.rd := by rw [m₇.rd, o₆.rd, o₅.rd, k₄.rd, k₃.rd, urd]
  refine wp_argS P (j := 13) (o := privBytes pc) (in_aR (by decide)) (by rw [m₇.gpr, g₆]) rd₇ (hmS f₇)
    (fun u₈ o₈ e₈ => ?_) ⟨by have := privBytes_rng pc; unfold arg frameBytes; omega_using [this],
      by have := privBytes_mod pc; unfold arg frameBytes; omega_using [this]⟩
  refine wp_subi fun u₉ o₉ e₉ => ?_
  refine wp_std (a := pb pc s + BitVec.ofNat 64 184) (by rw [o₉.get .r12, o₈.get .r12, m₇.gpr, g₆])
    (by rw [o₉.wr, o₈.wr, m₇.wr, o₆.wr, o₅.wr, w₄]; exact psa_in (by decide) (pbd (by decide))) fun u₁₀ m₁₀ => ?_
  have f₁₀ : Frame [PB pc s] t.mem u₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, o₈.mem]; exact f₇.writeW (List.mem_singleton_self _) _ (pb_in s (pbd (by decide)))
  show WP isa (.block (preArgs pc ++ _)) _ _
  rw [WP.block_append_iff]
  refine WP.mono (preArgs_ok P (u := u₁₀) (by rw [m₁₀.gpr, o₉.get .r12, o₈.get .r12, m₇.gpr, g₆])
    (by rw [m₁₀.rd, o₉.rd, o₈.rd, rd₇]) (by rw [m₁₀.wr, o₉.wr, o₈.wr, m₇.wr, o₆.wr, o₅.wr, w₄]) (hmS f₁₀))
    fun u₁₀' ⟨kp, fp, hp⟩ => ?_
  refine wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ => wp_mov fun u₁₃ o₁₃ e₁₃ =>
    wp_mov fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => wp_mov fun u₁₆ o₁₆ e₁₆ => wp_addi fun u₁₇ o₁₇ e₁₇ =>
    wp_mov fun w ow ew => wp_nil ?_
  have K : Keep [.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (allocated (privBytes pc) t) w :=
    ((k₃.trans (k₄.trans ((o₅.keep.trans o₆.keep).trans (m₇.keep.trans (o₈.keep.trans (o₉.keep.trans
      (m₁₀.keep.trans (kp.trans (o₁₁.keep.trans (o₁₂.keep.trans (o₁₃.keep.trans (o₁₄.keep.trans (o₁₅.keep.trans
      (o₁₆.keep.trans (o₁₇.keep.trans ow.keep)))))))))))))))).mono
  have kt : ∀ r ∉ [Reg.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], w.gpr r = t.gpr r :=
    fun r hr => by rw [K.gpr r hr]; rfl
  have K₁₀ : Keep [.r12, .r0, .r11] (allocated (privBytes pc) t) u₁₀ :=
    ((k₃.trans (k₄.trans ((o₅.keep.trans o₆.keep).trans (m₇.keep.trans (o₈.keep.trans (o₉.keep.trans
      m₁₀.keep))))))).mono
  have k10 : ∀ r ∉ [Reg.r12, .r0, .r11], u₁₀'.gpr r = t.gpr r := fun r hr => by
    rw [kp.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)), K₁₀.gpr r hr]; rfl
  have hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have v184 : u₉.gpr .r11 = psa s 11 := by rw [e₉, e₈]; exact sub_ofNat hl
  have v176 : u₆.gpr .r0 = psa s 10 := by
    rw [e₆, o₅.get .r14, e₅, k₄.get .r14, k₃.get .r14, ug, h.r14]; rfl
  have wm0 : w.mem = u₁₀'.mem := by
    rw [ow.mem, o₁₇.mem, o₁₆.mem, o₁₅.mem, o₁₄.mem, o₁₃.mem, o₁₂.mem, o₁₁.mem]
  have wm : u₁₀.mem = (u₇.mem.writeW (pb pc s + BitVec.ofNat 64 184) (psa s 11)) := by
    rw [m₁₀.mem, o₉.mem, o₈.mem, v184]
  have m7 : u₇.mem = (u₄.mem.writeW (pb pc s + BitVec.ofNat 64 176) (psa s 10)) := by
    rw [m₇.mem, o₆.mem, o₅.mem, v176]
  have fw : Frame [PB pc s] t.mem w.mem := by
    rw [wm0]
    exact f₁₀.trans (fp.sub fun r hr => ⟨PB pc s, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by have := privBytes_rng pc; omega_using [this])⟩)
  have sl : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [PB pc s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r :=
    fun hd r hr => by
      rw [List.mem_singleton.mp hr]
      have h := Offset.disjoint_below_above (fb s) (m := privBytes pc) (a := 0) (l := frameBytes)
        (by have := privBytes_rng pc; unfold frameBytes; omega_using [this])
      rw [BitVec.add_zero] at h
      exact (h.sub_right (Offset.sub_base _ hd)).symm
  have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ privBytes pc → b + 8 ≤ privBytes pc →
      Mem.Sep (pb pc s + BitVec.ofNat 64 a) (64 / 8) (pb pc s + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    Offset.sep _ h (by have := privBytes_rng pc; omega_using [ha, this]) (by have := privBytes_rng pc; omega_using [hb, this])
  have hpsa : ∀ i < nP pc, w.mem.readW (pb pc s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i := by
    intro i hi'
    rw [wm0]
    by_cases hi : i < 12
    rotate_left
    · cases pc with
      | false => exact absurd hi' (by simp only [nP, Bool.false_eq_true, ↓reduceIte]; omega_using [hi])
      | true =>
        rcases (by simp only [nP, ↓reduceIte] at hi'; omega_using [hi, hi'] : i = 12 ∨ i = 13) with rfl | rfl
        · exact (hp rfl).1
        · exact (hp rfl).2
    rw [fp.readW (r := ⟨pb pc s + BitVec.ofNat 64 (96 + 8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hi])) (by omega_using [hi]) (by have := privBytes_rng pc; omega_using [this])) (by decide), wm]
    by_cases h11 : i = 11
    · subst h11; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega_using [h11]) (by have := privBytes_rng pc; omega_using [hi, this]) (pbd (by decide))) (by decide), m7]
    by_cases h10 : i = 10
    · subst h10; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega_using [h10]) (by have := privBytes_rng pc; omega_using [hi, this]) (pbd (by decide))) (by decide)]
    have fr4 : ∀ {d : Nat}, d + 8 ≤ 112 → u₄.mem.readW (pb pc s + BitVec.ofNat 64 d) 64 =
        u₃.mem.readW (pb pc s + BitVec.ofNat 64 d) 64 := fun hd =>
      f₄.readW (r := ⟨pb pc s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl hd) (by omega_using [hd]) (by decide)) (by decide)
    by_cases h0 : i = 0
    · subst h0; rw [fr4 (by decide)]; exact r₃₉₆
    by_cases h1 : i = 1
    · subst h1; rw [fr4 (by decide)]; exact r₃₁₀₄
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega_using [h0, h1]⟩
      rw [show 96 + 8 * (j + 2) = 112 + 8 * j by omega_using [], got j (by omega_using [hi, h11, h10])]
      rcases (by omega_using [hi, h11, h10] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hemw : Spec.Rsa.bytesAt w.mem (off (Ss s) oEm) (kk s) = em := by
    rw [← hem]
    have hk2 : kk s ≤ 1024 := P.k2
    have hR : Region.Sub ⟨off (Ss s) oEm, kk s⟩ (scR s) := fun a ha =>
      sc_sub P a (VG.Proof.RsaOaep.PPC64LE.sc_in (S := Ss) (s := s) (by unfold oEm oRsa; omega_using [hk2]) a ha)
    have hd : (PB pc s).Disjoint ⟨off (Ss s) oEm, kk s⟩ := (P.ks.sub_left PB_sub).sub_right hR
    exact VG.Proof.RsaOaep.PPC64LE.bytes_entry (A := PB pc s) (B := PB pc s)
      (fw.mono fun r hr => by simp at hr ⊢; exact hr) hd hd
      (by have := (fits P).wS; unfold oEm oRsa at *; omega_using [hk2])
  refine ⟨by rw [K.sp, usp], by rw [K.rd, urd], by rw [K.wr, uwr], hmS fw, hemw,
    h.sv.sv.frame fw fun p hp r hr => sl (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr,
    by rw [fw.readW (Region.contains_self _ _) (sl (by decide)) (by decide)]; exact h.sv.ls,
    fun r hr => by rw [kt r (by revert r; decide)]; exact h.sv.hi r hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpsa⟩
  · rw [ow.get .r3, o₁₇.get .r3, o₁₆.get .r3, o₁₅.get .r3, o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, e₁₁,
      k10 .r16 (by decide), Base.r16 h]
  · rw [ow.get .r4, o₁₇.get .r4, o₁₆.get .r4, o₁₅.get .r4, o₁₄.get .r4, o₁₃.get .r4, e₁₂, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]
  · rw [ow.get .r5, o₁₇.get .r5, o₁₆.get .r5, o₁₅.get .r5, o₁₄.get .r5, e₁₃, o₁₂.get .r20, o₁₁.get .r20,
      k10 .r20 (by decide), Base.r20 h]
  · rw [ow.get .r6, o₁₇.get .r6, o₁₆.get .r6, o₁₅.get .r6, e₁₄, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]
  · rw [ow.get .r7, o₁₇.get .r7, o₁₆.get .r7, e₁₅, o₁₄.get .r21, o₁₃.get .r21, o₁₂.get .r21, o₁₁.get .r21,
      k10 .r21 (by decide), Base.r21 h]
  · rw [ow.get .r8, o₁₇.get .r8, e₁₆, o₁₅.get .r22, o₁₄.get .r22, o₁₃.get .r22, o₁₂.get .r22, o₁₁.get .r22,
      k10 .r22 (by decide), Base.r22 h]
  · rw [ow.get .r9, e₁₇, o₁₆.get .r14, o₁₅.get .r14, o₁₄.get .r14, o₁₃.get .r14, o₁₂.get .r14, o₁₁.get .r14,
      k10 .r14 (by decide), h.r14]
  · rw [ew, o₁₇.get .r15, o₁₆.get .r15, o₁₅.get .r15, o₁₄.get .r15, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]

end

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


/-!
# RSASSA-PSS signing on PPC64LE: the private operation

Untrusted: everything here is checked by Lean. The call's narrowed entry
state (`callE`: it reads `n`, `e`, `EM`, the private key and its stack
arguments, and writes `out` and the rest of `scratch`), its precondition
(`preP_at`) and regions (`call_covers`); `priv_ok`: the private operation's
frame, its arguments and the call of `vg_rsa_private_checked` write RSASP1
of `EM`, checked against `e`, to `out` and return its code (`privOut`), and
leave what the restores need.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx hiRegs kR fb fr Saves saved_offs)

/-- `out`, `EM` and the rest of `scratch`. -/
abbrev outR (s : State) : Region := ⟨s.gpr .r3, kk s⟩
abbrev emR (s : State) : Region := ⟨off (Ss s) oEm, kk s⟩
abbrev rsR (s : State) : Region := ⟨Ss s + BitVec.ofNat 64 oRsa, ((stackArg s 13).toNat - 1024) * 8⟩
/-- The call's stack arguments. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨pb pc s + BitVec.ofNat 64 96, if pc then 112 else 96⟩

/-- The regions the call reads and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, emR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [psaR pc s]
abbrev callWr (s : State) : List Region := [outR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_sp (s t : State) : (callE pc s t).sp = t.sp := rfl

theorem callE_stackArg {s t : State} {em : List Byte} (A : AtPriv pc s em t) {i : Nat} (hi : i < nP pc) :
    stackArg (callE pc s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, callE_sp, A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega_using []]
  exact A.psa i hi

theorem callE_addr {s t : State} {em : List Byte} (A : AtPriv pc s em t) :
    stackArgAddr (callE pc s t) 0 = pb pc s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, callE_sp, A.sp]

theorem priv_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.code = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

theorem privP_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.codeP = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

section
variable {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem em_sub : Region.Sub (emR s) (scR s) := fun a ha =>
  sc_sub P a (VG.Proof.RsaOaep.PPC64LE.sc_in (S := Ss) (s := s) (by have := P.k2; unfold kk oEm oRsa at *; omega_using [this]) a ha)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this
  exact Offset.sub_base _ (by unfold oRsa; omega_using [this])

omit P in
theorem psa_subS : Region.Sub (psaR pc s) (kS pc s) := pb_sub s (by have := privBytes_rng pc; cases pc <;> decide)

theorem em_rs : (emR s).Disjoint (rsR s) := by
  have h := Offset.disjoint_base (Ss s) (d := oRsa) (n := ((stackArg s 13).toNat - 1024) * 8) (k := kk s)
    (by have := P.k2; unfold kk oRsa; omega_using [this]) (by have := P.wsc; have := scLen P; unfold oRsa at *; omega_arith)
  have e : emR s = ⟨Ss s, kk s⟩ := by simp only [emR, off, show oEm = 0 from rfl, BitVec.add_zero]
  rw [e]; exact h.symm

theorem out_eq : outR s = oR s := by simp only [outR, oR, kk, P.ok]

omit P in
theorem kD'_sub : Region.Sub ⟨s.sp - BitVec.ofNat 64 (stackBytes pc), Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kS pc s) := by
  have := Offset.sub_base (s.sp - BitVec.ofNat 64 (stackBytes pc)) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
    (k := stackBytes pc) (by have := stackBytes_ge pc; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [this])
  rwa [BitVec.add_zero] at this

theorem preP_at {t : State} {em : List Byte} (A : AtPriv pc s em t) : Rsa.PPC64LE.Priv.PreP pc (callE pc s t) := by
  have hk := P.k2
  have hk1 := P.k1
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  have hsp : (callE pc s t).sp = pb pc s := A.sp
  have sp1 := P.sp1
  have pr := privBytes_rng pc
  have hpbt : (pb pc s).toNat = s.sp.toNat - (256 + privBytes pc) := by
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes pc)
      (by unfold frameBytes; omega_using [pr])]
    unfold stackBytes Impl.Rsa.PPC64LE.Priv.frameBytes at sp1; unfold frameBytes at *; omega_using [sp1]
  have g3 : (callE pc s t).gpr .r3 = s.gpr .r3 := (callE_gpr s t).trans A.r3
  have g4 : (callE pc s t).gpr .r4 = s.gpr .r6 := (callE_gpr s t).trans A.r4
  have g5 : (callE pc s t).gpr .r5 = s.gpr .r5 := (callE_gpr s t).trans A.r5
  have g6 : (callE pc s t).gpr .r6 = s.gpr .r6 := (callE_gpr s t).trans A.r6
  have g7 : (callE pc s t).gpr .r7 = s.gpr .r7 := (callE_gpr s t).trans A.r7
  have g8 : (callE pc s t).gpr .r8 = s.gpr .r8 := (callE_gpr s t).trans A.r8
  have g9 : (callE pc s t).gpr .r9 = off (Ss s) oEm := (callE_gpr s t).trans A.r9
  have g10 : (callE pc s t).gpr .r10 = s.gpr .r6 := (callE_gpr s t).trans A.r10
  have hO : Rsa.PPC64LE.Priv.oR (callE pc s t) = oR s := by
    simp only [Rsa.PPC64LE.Priv.oR, g3, g4, oR, P.ok]
  have hN : Rsa.PPC64LE.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  have hE : Rsa.PPC64LE.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  have hI : Rsa.PPC64LE.Priv.iR (callE pc s t) = emR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10, emR, kk]
  have hP : Rsa.PPC64LE.Priv.pR (callE pc s t) = pR s := by
    simp only [Rsa.PPC64LE.Priv.pR, sa 0 (by decide), sa 1 (by decide)]; rfl
  have hQ : Rsa.PPC64LE.Priv.qR (callE pc s t) = qR s := by
    simp only [Rsa.PPC64LE.Priv.qR, sa 2 (by decide), sa 3 (by decide)]; rfl
  have hDP : Rsa.PPC64LE.Priv.dpR (callE pc s t) = dpR s := by
    simp only [Rsa.PPC64LE.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]; rfl
  have hDQ : Rsa.PPC64LE.Priv.dqR (callE pc s t) = dqR s := by
    simp only [Rsa.PPC64LE.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]; rfl
  have hQI : Rsa.PPC64LE.Priv.qiR (callE pc s t) = qiR s := by
    simp only [Rsa.PPC64LE.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]; rfl
  have hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have w11 : (BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)).toNat = (stackArg s 13).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 13).isLt; omega_using [])]
  have hS : Rsa.PPC64LE.Priv.sR (callE pc s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hA : Rsa.PPC64LE.Priv.aR pc (callE pc s t) = psaR pc s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  have hK : Rsa.PPC64LE.Priv.kR (callE pc s t) = ⟨s.sp - BitVec.ofNat 64 (stackBytes pc),
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  have kD' := kD'_sub (pc := pc) (s := s)
  have ka : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 (stackBytes pc), Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR pc s) := by
    show Region.Disjoint _ ⟨pb pc s + BitVec.ofNat 64 96, if pc then 112 else 96⟩
    rw [pb_base, Offset.add_add]
    cases pc <;> exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  have es := em_sub P
  have rss := rs_sub P
  have ps : Region.Sub (psaR pc s) (kS pc s) := psa_subS
  have s1 := sa 1 (by decide)
  have s3 := sa 3 (by decide)
  have s5 := sa 5 (by decide)
  have s7 := sa 7 (by decide)
  have s9 := sa 9 (by decide)
  have s11 := sa 11 (by decide)
  simp only [psa] at s1 s3 s5 s7 s9 s11
  have wS : (Ss s + BitVec.ofNat 64 oRsa).toNat = (stackArg s 12).toNat + oRsa := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oRsa) (by decide),
      Nat.mod_eq_of_lt (by
        have e : (Ss s).toNat = (stackArg s 12).toNat := rfl
        have := P.wsc; have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords oRsa at *; omega_arith)]
  have q1 : Impl.Rsa.PPC64LE.Priv.frameBytes ≤ (callE pc s t).sp.toNat := by
    rw [hsp, hpbt]; unfold stackBytes at sp1; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [sp1]
  have q2 : (callE pc s t).sp.toNat + 192 ≤ 2 ^ 64 := by rw [hsp, hpbt]; have := P.sp2; omega_using []
  have hkk : kk s = (s.gpr .r6).toNat := rfl
  refine ⟨q1, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show callRd pc s = Rsa.PPC64LE.Priv.rdL pc (callE pc s t)
    simp only [Rsa.PPC64LE.Priv.rdL, hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]
    cases pc
    · rfl
    · simp only [↓reduceIte, Rsa.PPC64LE.Priv.preR, callE_stackArg A (i := 12) (by decide),
        callE_stackArg A (i := 13) (by decide), psa]
      rfl
  · rw [hO, hS, ← out_eq P]; rfl
  · rw [hO, hN]; exact P.on
  · rw [hO, hE]; exact P.oe
  · rw [hO, hI]; exact P.os.sub_right es
  · rw [hO, hP]; exact P.op
  · rw [hO, hQ]; exact P.oq
  · rw [hO, hDP]; exact P.odp
  · rw [hO, hDQ]; exact P.odq
  · rw [hO, hQI]; exact P.oqi
  · rw [hO, hS]; exact P.os.sub_right rss
  · rw [hO, hA]; exact (P.ko.sub_left ps).symm
  · rw [hN, hS]; exact P.ns.sub_right rss
  · rw [hE, hS]; exact P.es.sub_right rss
  · rw [hI, hS]; exact em_rs P
  · rw [hP, hS]; exact P.ps.sub_right rss
  · rw [hQ, hS]; exact P.qs.sub_right rss
  · rw [hDP, hS]; exact P.dps.sub_right rss
  · rw [hDQ, hS]; exact P.dqs.sub_right rss
  · rw [hQI, hS]; exact P.qis.sub_right rss
  · rw [hS, hA]; exact ((P.ks.sub_left ps).sub_right rss).symm
  · rw [hK, hO]; exact P.ko.sub_left kD'
  · rw [hK, hN]; exact P.kn.sub_left kD'
  · rw [hK, hE]; exact P.ke.sub_left kD'
  · rw [hK, hI]; exact (P.ks.sub_left kD').sub_right es
  · rw [hK, hP]; exact P.kp.sub_left kD'
  · rw [hK, hQ]; exact P.kq.sub_left kD'
  · rw [hK, hDP]; exact P.kdp.sub_left kD'
  · rw [hK, hDQ]; exact P.kdq.sub_left kD'
  · rw [hK, hQI]; exact P.kqi.sub_left kD'
  · rw [hK, hS]; exact (P.ks.sub_left kD').sub_right rss
  · rw [hK, hA]; exact ka
  · rw [g3, g4]; have := P.wo; rw [P.ok] at this; exact this
  · rw [g5, g6]; exact P.wn
  · rw [g7, g8]; exact P.we
  · rw [g9, g10]
    show (Ss s + BitVec.ofNat 64 oEm).toNat + _ ≤ _
    rw [show oEm = 0 from rfl, BitVec.add_zero]
    show (stackArg s 12).toNat + _ ≤ _; have := P.wsc; have := scLen P; unfold oRsa at *; omega_using [hk, wS]
  · rw [sa 0 (by decide), s1]; exact P.wp
  · rw [sa 2 (by decide), s3]; exact P.wq
  · rw [sa 4 (by decide), s5]; exact P.wdp
  · rw [sa 6 (by decide), s7]; exact P.wdq
  · rw [sa 8 (by decide), s9]; exact P.wqi
  · rw [sa 10 (by decide), s11, w11]; simp only [psa]; rw [wS]; have := P.wsc; unfold oRsa; omega_using [hl, this]
  · rw [g6]; exact hk1
  · rw [g6]; exact hk
  · rw [g4, g6]
  · rw [g10, g6]
  · rw [g8]; exact P.e1
  · rw [g8, g6]; exact P.e2
  · rw [s1]; exact P.p1
  · rw [s1, g6]; exact P.p2
  · rw [s3]; exact P.q1
  · rw [s3, g6]; exact P.q2
  · rw [s5, s1]; exact P.h3
  · rw [s9, s1]; exact P.h7
  · rw [s7, s3]; exact P.h5
  · rw [g6, s11, w11]; have := P.hs; unfold Spec.RsaPss.scratchWords at this; omega_using [this]

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 13).toNat * 8) :
    Covers [⟨Ss s + BitVec.ofNat 64 d, n⟩] s.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} {em : List Byte} (A : AtPriv pc s em t) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · rw [out_eq P]
      exact Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [P.hwr]; simp))
    · have := cov_sc P (d := oRsa) (n := ((stackArg s 13).toNat - 1024) * 8) (by unfold oRsa; omega_using [hl])
      exact fun a n hi => let ⟨r, hr, hc⟩ := this a n hi; ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  have hleft : r ∈ rdS pc D s → Covers [r] (rdS pc D s ++ ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ ::
      fr s :: s.wr) := fun h => Covers.left (Covers.of_mem fun r' hr' => by rw [List.mem_singleton.mp hr']; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact hleft (by simp)
  · exact hleft (by simp)
  · have := cov_sc P (d := oEm) (n := kk s) (by have := scLen P; have := P.k2; unfold kk oEm oRsa at *; omega_using [hl, this])
    exact Covers.right fun a n hi => let ⟨r, hr, hc⟩ := this a n hi;
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  · exact hleft (by simp)
  · exact hleft (by simp)
  · exact hleft (by simp)
  · exact hleft (by simp)
  · exact hleft (by simp)
  · cases pc
    · simp at hp
    · simp only [↓reduceIte, List.mem_singleton] at hp
      subst hp; exact hleft (by simp)
  · exact Covers.right (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩, List.mem_cons_self .., 64, by
        show pb pc s + BitVec.ofNat 64 96 = pb pc s + BitVec.ofNat 64 32 + BitVec.ofNat 64 64
        rw [Offset.add_add], by show 64 + (if pc then 112 else 96) ≤ privBytes pc - 32; cases pc <;> decide⟩)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} {em : List Byte} (A : AtPriv pc s em t) {R : Region} (hd : (kS pc s).Disjoint R)
    (hs : (SC Ss s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaOaep.PPC64LE.bytes_entry A.mem hd hs hl

omit P in
theorem fb_base (s : State) :
    fb s = (s.sp - BitVec.ofNat 64 (stackBytes pc)) + BitVec.ofNat 64 (stackBytes pc - frameBytes) := by
  rw [← Offset.sub_sub_eq, Offset.ofNat_sub_ofNat (by have := stackBytes_ge pc; unfold frameBytes; omega_using []),
    show stackBytes pc - (stackBytes pc - frameBytes) = frameBytes by have := stackBytes_ge pc; unfold frameBytes; omega_using [this]]

/-- The slots of our frame and what the call writes. -/
theorem slot_dis {d : Nat} (hd : d + 8 ≤ frameBytes) :
    ∀ r ∈ callWr s ++ [below (pb pc s) Impl.Rsa.PPC64LE.Priv.frameBytes],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  have pr := privBytes_rng pc
  have hk : Region.Sub ⟨fb s + BitVec.ofNat 64 d, 8⟩ (kS pc s) := by
    rw [fb_base, Offset.add_add]
    exact Offset.sub_base _ (by unfold stackBytes; unfold frameBytes at *; omega_using [hd])
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [out_eq P]; exact P.ko.sub_left hk
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · have e : below (pb pc s) Impl.Rsa.PPC64LE.Priv.frameBytes =
        ⟨(s.sp - BitVec.ofNat 64 (stackBytes pc)) + BitVec.ofNat 64 0, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
      simp only [below, pb_base, BitVec.add_sub_cancel, BitVec.add_zero]
    rw [e, fb_base, Offset.add_add]
    exact Offset.disjoint _ (.inr (by unfold stackBytes; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using []))
      (by unfold stackBytes; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd, pr]) (by decide)

omit P in
/-- With `pc`, the facts of `pre` at the call. -/
theorem preX_at {t : State} {em : List Byte} (P' : PreS true D s) (X : PreXS s) (A : AtPriv true s em t) :
    Rsa.PPC64LE.Priv.PreX (callE true s t) := by
  have sa := fun i (hi : i < 14) => callE_stackArg A (i := i) hi
  have hsp : (callE true s t).sp = pb true s := A.sp
  have hpbt : (pb true s).toNat = s.sp.toNat - 464 := by
    have sp1 := P'.sp1
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes true) (by decide)]
    rw [stackBytes_true] at sp1; unfold frameBytes; simp only [privBytes, ↓reduceIte]; omega_using [sp1]
  have hPre : Rsa.PPC64LE.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.PPC64LE.Priv.preR, sa 12 (by decide), sa 13 (by decide), psa]
  have hO : Rsa.PPC64LE.Priv.oR (callE true s t) = oR s := by
    simp only [Rsa.PPC64LE.Priv.oR, callE_gpr s t (r := .r3), callE_gpr s t (r := .r4), A.r3, A.r4, oR, P'.ok]
  have hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P'.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have w11 : (BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)).toNat = (stackArg s 13).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 13).isLt; omega_using [])]
  have hS : Rsa.PPC64LE.Priv.sR (callE true s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hK : Rsa.PPC64LE.Priv.kR (callE true s t) = ⟨s.sp - BitVec.ofNat 64 (stackBytes true),
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  refine ⟨by rw [hO, hPre]; exact X.oP, by rw [hS, hPre]; exact X.sP.sub_left (rs_sub P'),
    by rw [hK, hPre]; exact X.kP.sub_left kD'_sub, ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr s t (r := .r6), A.r6]; exact X.pl
  · rw [hsp, hpbt]; have := P'.sp2; omega_using []
  · -- `pre`'s values, as the caller's precondition gives them.
    have hb := fun {p : Addr} {len : Nat} (hd : (kS true s).Disjoint ⟨p, len⟩) (hs : (scR s).Disjoint ⟨p, len⟩)
      (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd (hs.sub_left (sc_sub P')) hl
    have hw := VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (p := stackArg s 16) (n := (stackArg s 17).toNat)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [Nat.mul_comm]; exact X.kP.symm
        · rw [Nat.mul_comm]; exact (X.sP.sub_left (sc_sub P')).symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.PPC64LE.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem, callE_gpr s t (r := .r5),
      callE_gpr s t (r := .r6), A.r5, A.r6, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide),
      sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), psa, hw]
    rw [hb P'.kn P'.ns.symm (by have := P'.wn; omega_using []), hb P'.kp P'.ps.symm (by have := P'.wp; omega_using []),
      hb P'.kq P'.qs.symm (by have := P'.wq; omega_using [])]
    exact X.hyp rfl

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv {u : State} {em : List Byte} (X : pc = true → PreXS s) (A : AtPriv pc s em u) :
    WP isa (privCall pc) u fun v => v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      Frame (callWr s ++ [below (pb pc s) Impl.Rsa.PPC64LE.Priv.frameBytes]) u.mem v.mem ∧
      (∀ r ∈ preserved, v.gpr r = u.gpr r) ∧
      Rsa.PPC64LE.Priv.fnPost (callE pc s u) (v.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers P A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      (Rsa.PPC64LE.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp' hf hpres hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp', hf, hpres, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      (Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P A) (preX_at P (X rfl) A)) hc hw
      (fun v hrd hwr hsp' hf hpres hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp', hf, hpres, hpost⟩

/-- After the private operation. -/
def AfterS (pc : Bool) (s : State) (em : List Byte) (w : State) : Prop :=
  Saves s w ∧ w.rd = s.rd ∧
    (HypS pc s → Spec.Rsa.writtenOutcome w.mem (s.gpr .r3) (kk s) ((w.gpr .r3).setWidth 32) (privOut s em))

theorem priv_ok {t : State} (X : pc = true → PreXS s) (h : Base Ss vS s t) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em) : WP isa (priv pc) t (AfterS pc s em) := by
  have hsp : t.sp = fb s := h.sv.sp
  have hk := P.k2
  have pr := privBytes_rng pc
  unfold priv
  refine WP.alloc (by cases pc <;> exact ⟨by decide, by decide, by decide⟩) (by
    rw [hsp]; have := P.sp1
    rw [fb, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes) (by decide)]
    unfold stackBytes at this; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [this]) ?_
  refine WP.seq (WP.mono (privArgs_ok P h hem) fun u A => ?_)
  refine WP.mono (call_priv P X A) fun v ⟨hrd, hwr, hsp', hf, hpres, hpost⟩ => ?_
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  have hb := fun {p : Addr} {len : Nat} (hd : (kS pc s).Disjoint ⟨p, len⟩) (hs : (scR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd (hs.sub_left (sc_sub P)) hl
  -- The state after the frame's release.
  have fsp : (freed (privBytes pc) v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 (privBytes pc) = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  have fwr : (freed (privBytes pc) v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  have svs : Spill.Saved (fb s) s.gpr saved v.mem :=
    A.sv.frame hf fun p hp r hr => slot_dis P (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr
  have lss : v.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
    rw [hf.readW (Region.contains_self _ _) (slot_dis P (by decide)) (by decide)]; exact A.ls
  refine ⟨⟨fsp, fwr, fun r hr => ?_, svs, lss⟩, by show v.rd = _; exact hrd.trans A.rd, fun hyp => ?_⟩
  · show v.gpr r = _; rw [hpres r (by revert r; decide)]; exact A.hi r hr
  simp only [Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr s u (r := .r3), callE_gpr s u (r := .r5), callE_gpr s u (r := .r6),
    callE_gpr s u (r := .r7), callE_gpr s u (r := .r8), callE_gpr s u (r := .r9), A.r3, A.r5, A.r6, A.r7, A.r8,
    A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 4 (by decide),
    sa 6 (by decide), sa 8 (by decide), psa] at hpost
  rw [A.em, hb P.kn P.ns.symm (by have := P.wn; omega_using []), hb P.ke P.es.symm (by have := P.we; omega_using []),
    hb P.kp P.ps.symm (by have := P.wp; omega_using []), hb P.kq P.qs.symm (by have := P.wq; omega_using []),
    hb (by have := P.kdp; simp only [dpR, P.h3] at this; exact this)
      (by have := P.dps; simp only [dpR, P.h3] at this; exact this.symm) (by have := P.wdp; rw [P.h3] at this; omega_using []),
    hb (by have := P.kdq; simp only [dqR, P.h5] at this; exact this)
      (by have := P.dqs; simp only [dqR, P.h5] at this; exact this.symm) (by have := P.wdq; rw [P.h5] at this; omega_using []),
    hb (by have := P.kqi; simp only [qiR, P.h7] at this; exact this)
      (by have := P.qis; simp only [qiR, P.h7] at this; exact this.symm) (by have := P.wqi; rw [P.h7] at this; omega_using [])]
    at hpost
  exact hpost

end
end VG.Proof.RsaPss.PPC64LE.Sg
