module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreA
public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreR2
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: the modulus's values first

`partN_ok`: after the checks (`A`), `n`'s values to `pre` (`setupN`,
`Precompute.core`, in the working space laid out for `w` words at `X`'s base,
which leaves `X`'s arrays 4 and 5 as they are), then `R² mod n` from `pre`
into `X`'s array 6, zero-extended to its `2 w` words (`xIn`), for the
factors' `R² mod p` (`AN`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Crt (cmask wordsOf savW)

/-- An address in the region at `B + o` of `n` bytes is at those offsets. -/
theorem in_of_contains {B y : Addr} {o n : Nat} (h : (⟨Mont.off B o, n⟩ : Region).Contains y 1)
    (hn : o + n ≤ 2 ^ 64) : o ≤ (y - B).toNat ∧ (y - B).toNat < o + n := by
  have I := Offset.lt_iff y B hn
  change (y - Mont.off B o).toNat + 1 ≤ n at h
  exact I.mp (by change (y - Mont.off B o).toNat < n; omega_arith)

theorem ofs_off' (B : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    (Mont.off B d + BitVec.ofNat 64 i - B).toNat = d + i := Mont.ofs_off B h

/-- The registers `setupN` writes. -/
def nRegs : List Reg := [.s5, .s7, .s8, .t0, .a1, .a7, .a2, .a5, .a6]

/-- `setupN`, after the checks: `Precompute.core`'s registers. -/
theorem setupN_ok {s₀ u : State} (hP : PF s₀) (hB : A s₀ u) :
    WP isa (.block PrivPre.setupN) u fun v =>
      (v.gpr .s5 = s₀.gpr .a0 ∧ v.gpr .s7 = s₀.gpr .a2 ∧ v.gpr .s8 = BitVec.ofNat 64 (ck s₀) ∧
        v.gpr .t0 = BitVec.ofNat 64 (cw s₀) ∧
        v.gpr .a7 = Mont.off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .a2 = Mont.off (cS s₀) (slot (cw s₀) 1) ∧
        v.gpr .a5 = Mont.off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .a6 = Mont.off (cS s₀) (slot (cw s₀) 3) ∧
        v.mem = u.mem) ∧
      Keep nRegs u v := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have hs := hB.scr
  have z : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
  have hO : u.mem.readW (cS s₀) 64 = s₀.gpr .a0 := by rw [← z]; exact hB.hOut
  have l0 : InRegions (u.rd ++ u.wr) (cS s₀) 8 := by rw [← z]; exact hs.ld (by omega_arith)
  have hN : u.mem.readW (Mont.off (cS s₀) 8) 64 = s₀.gpr .a2 := hB.hN
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have hK : u.mem.readW (Mont.off (cS s₀) 16) 64 = BitVec.ofNat 64 K := by
    rw [← hKe]; exact hB.hNL.trans (Pre.ofNat_toNat64 _).symm
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold PrivPre.setupN
  brun [hB.s6, add_ofNat_zero, oOut, oN, oNLen, l0, hs.al, hs.ld (show 8 + 8 ≤ cZ s₀ by omega_arith),
    hs.al8 (show 8 + 8 ≤ cZ s₀ by omega_arith) (by decide), hs.ld (show 16 + 8 ≤ cZ s₀ by omega_arith),
    hs.al8 (show 16 + 8 ≤ cZ s₀ by omega_arith) (by decide), hO, hN, hK,
    Pre.ofNat_add7_shr3 K (by omega_arith), Pre.ofNat_shl3, hdrBytes]
  rw [dw, hKe]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Mont.off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat] <;>
    congr 2 <;> omega_arith

/-- A word of `pre` from `n`, after `core` (which writes `n`'s values in
`pre`'s first `n` bytes and arrays in the working space). -/
theorem core_word_pre {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨Mont.off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : n ≤ d) (hd' : d + 8 ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64)
    (hPn : P.toNat + PL ≤ 2 ^ 64) : Mont.word m' P d = Mont.word m P d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx := ofs_off' P (d := d) (i := i) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by omega_arith)
    have := hsep (Mont.off P d + BitVec.ofNat 64 i) (by change (_ - P).toNat < PL; omega_arith)
    change _ ≤ (_ - S).toNat at this
    omega_arith
  · change (_ - P).toNat + 1 ≤ n at hc
    omega_arith

/-- A word of the header, after `core`. -/
theorem core_word_hdr {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨Mont.off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : d + 8 ≤ hdrBytes) (hn : n ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64) :
    Mont.word m' S d = Mont.word m S d := by
  have hh : hdrBytes = 256 := rfl
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx := ofs_off' S (d := d) (i := i) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by omega_arith)
    omega_arith
  · change (_ - P).toNat + 1 ≤ n at hc
    by_contra hne
    have := hsep (Mont.off S d + BitVec.ofNat 64 i) (by change (_ - P).toNat < PL; omega_arith)
    change _ ≤ (_ - S).toNat at this
    omega_arith

theorem sub_len {P : Addr} {n k : Nat} (h : n ≤ k) : Region.Sub ⟨P, n⟩ ⟨P, k⟩ := fun _ hx => by
  simp only [Region.Contains] at hx ⊢; omega_arith

/-- The words of `wordsAt` from `word`s. -/
theorem wordsAt_eq {m m' : Mem} {P : Addr} {n : Nat} (h : ∀ i < n, Mont.word m P (8 * i) = Mont.word m' P (8 * i)) :
    Spec.Rsa.wordsAt m P n = Spec.Rsa.wordsAt m' P n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `pre`'s first `16 w` bytes, in a state with `s₀`'s writable regions. -/
theorem pre16 {s₀ s : State} (hP : PF s₀) (h : s.wr = s₀.wr) : Scr s (s₀.gpr .a0) (16 * cw s₀) := by
  have hpl := hP.preLen
  exact Crt.Scr.le (hP.pre.congr h) (by omega_arith)

/-- The working space is apart from `pre`'s first `16 w` bytes. -/
theorem sep16 {s₀ : State} (hP : PF s₀) : ∀ x, ofs (cS s₀) x < cZ s₀ → 16 * cw s₀ ≤ ofs (s₀.gpr .a0) x :=
  fun x hx => by
    have hpl := hP.preLen
    refine Nat.le_of_not_lt fun hc => ?_
    have := hP.sepPre x (by omega_arith)
    omega_arith

/-- `n` fits its `w = ⌈k / 8⌉` words. -/
theorem cN_lt (s₀ : State) : cN s₀ < 2 ^ (64 * cw s₀) := by
  have h := Crt.os2ip_lt' (nB s₀) (VG.Proof.Bignum.bytesAt_length _ _ _)
  rw [VG.Proof.Bignum.pow256_eq] at h
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by simp only [cw, ck]; omega_arith))

/-- Under a set mask, `n` is odd and its top word is not zero. -/
theorem n_facts {s₀ : State} (hb : cb s₀ = true) : cN s₀ % 2 = 1 ∧ 2 ^ (64 * (cw s₀ - 1)) ≤ cN s₀ := by
  simp only [cb, privMask, Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨h1, _⟩, _⟩, h4⟩, _⟩ := hb
  refine ⟨h1, Nat.le_trans ?_ h4⟩
  rw [VG.Proof.Bignum.pow256_eq]
  exact Nat.pow_le_pow_right (by decide) (by simp only [cw]; omega_arith)

theorem shl1_ofNat {w : Nat} (_h : w < 2 ^ 31) : BitVec.ofNat 64 w <<< 1 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem shr1_ofNat {w : Nat} (_h : w < 2 ^ 31) : BitVec.ofNat 64 (2 * w) >>> 1 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- `R_n² mod n`, zero-extended to `L ≥ w` words, mod a factor `P` of `n`:
the value `prime`'s `R_p² mod p` starts from (`PArgs.hx6`). -/
theorem ext_mod {m : Mem} {B : Addr} {d w L N P : Nat} (hx : wordsVal m B d w = 2 ^ (128 * w) % N)
    (hz : ∀ i, w ≤ i → i < L → Mont.word m B (d + 8 * i) = 0) (hwL : w ≤ L) (hPN : P ∣ N) :
    wordsVal m B d L % P = 2 ^ (128 * w) % P := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hwL
  have hz' : ∀ i < j, Mont.word m B (d + 8 * w + 8 * i) = 0 := fun i hi => by
    rw [Nat.add_assoc, ← Nat.mul_add]
    exact hz (w + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left hi _)
  rw [fios_wordsVal_append, wordsVal_zero hz', Nat.mul_zero, Nat.add_zero, hx, Nat.mod_mod_of_dvd _ hPN]

/-- The number of words `prime` reduces, `w_A ⌈w / w_A⌉`, is in `[w, 2 w)`. -/
theorem chunks_bounds {w wA : Nat} (h2 : 2 ≤ wA) (hw : wA ≤ w) :
    w ≤ wA * Win.nChunks w wA ∧ wA * Win.nChunks w wA < 2 * w := by
  have h1 := Win.le_nChunks_mul (K := w) (w := wA) (by omega_using [h2])
  have h3 := Win.nChunks_mul_lt (K := w) (w := wA) (by omega_using [h2]) (by omega_using [h2, hw])
  rw [Nat.mul_comm]; omega_using [hw, h1, h3]

/-! ## `R² mod n` into `X`'s array 6 -/

/-- `xIn`: `R² mod n` (`pre`'s words `w` to `2 w`, at `s5`) into `X`'s array 6
(at `s6`, `s11`), zero-extended to its `2 w` words, for `t0 = w`. -/
theorem xIn_ok {v : State} {S P : Addr} {Z w : Nat} (hs : Scr v S Z) (hp : Scr v P (16 * w))
    (hsep : ∀ x, ofs P x < 16 * w → Z ≤ ofs S x) (hw : 1 ≤ w) (hw' : w < 2 ^ 29)
    (h6 : v.gpr .s6 = S) (h11 : v.gpr .s11 = BitVec.ofNat 64 (8 * (2 * w + 2)))
    (h0 : v.gpr .t0 = BitVec.ofNat 64 w) (h5 : v.gpr .s5 = P) (hZ : slot (2 * w) 7 ≤ Z) :
    WP isa PrivPre.xIn v fun u =>
      ((∀ i < w, word u.mem S (slot (2 * w) 6 + 8 * i) = word v.mem P (8 * w + 8 * i)) ∧
        (∀ i, w ≤ i → i < 2 * w → word u.mem S (slot (2 * w) 6 + 8 * i) = 0) ∧
        Outside S (slot (2 * w) 6) (8 * (2 * w)) v.mem u.mem ∧ u.gpr .t0 = BitVec.ofNat 64 w) ∧
      Keep [.t3, .t0, .s0, .t4, .t5] v u := by
  have hn := hs.nowrap
  have hnp := hp.nowrap
  have es : ∀ j, slot (2 * w) j = 256 + j * (8 * (2 * w + 2)) := fun _ => rfl
  have e6 := es 6; have e7 := es 7
  unfold PrivPre.xIn
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Win.xbase_ok (rd := .t3) (by decide) h6 h11 6) fun v₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t0] (Q := fun u => u.gpr .t0 = BitVec.ofNat 64 (2 * w) ∧ u.mem = v₁.mem)
    (by brun [(k1.gpr (by decide)).trans h0, shl1_ofNat (show w < 2 ^ 31 by omega_arith)]) (by rfl) (by rfl))
    fun v₂ ⟨⟨a0, m2⟩, k2⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr (k1.trans k2).2.2) ((k2.gpr (by decide)).trans a3) a0
    (by omega_arith) (by omega_arith) (by unfold slot hdrBytes; omega_arith) (by omega_arith))
    fun v₃ ⟨⟨_, z3, o3⟩, k3⟩ => ?_)
  have hm2 : v₂.mem = v.mem := by rw [m2, m1]
  rw [hm2] at o3
  have k13 := (k1.trans k2).trans k3
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t0] (Q := fun u => u.gpr .t0 = BitVec.ofNat 64 w ∧ u.mem = v₃.mem)
    (by brun [(k3.gpr (by decide)).trans a0, shr1_ofNat (show w < 2 ^ 31 by omega_arith)]) (by rfl) (by rfl))
    fun v₄ ⟨⟨b0, m4⟩, k4⟩ => ?_
  refine WP.mono (Win.xbase_ok (rd := .t3) (by decide) (((k13.trans k4).gpr (by decide)).trans h6)
    (((k13.trans k4).gpr (by decide)).trans h11) 6) fun v₅ ⟨⟨b3, m5⟩, k5⟩ => ?_
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = Mont.off P (8 * w) ∧ u.mem = v₅.mem)
    (by
      brun [(k5.gpr (by decide)).trans b0, ((k13.trans (k4.trans k5)).gpr (by decide)).trans h5, Pre.ofNat_shl3])
      (by rfl) (by rfl)) fun v₆ ⟨⟨c4, m6⟩, k6⟩ => ?_
  have k46 := (k4.trans k5).trans k6
  have hm6 : v₆.mem = v₃.mem := by rw [m6, m5, m4]
  have hp6 : Scr v₆ P (16 * w) := hp.congr (k13.trans k46).2.2
  refine WP.mono (Pub.copyIn_ok (B := S) (P := P) (Zp := 16 * w) (dS := 8 * w) (dD := slot (2 * w) 6) (w := w)
    (hs.congr (k13.trans k46).2.2) hnp (fun i hi => hp6.ld (by omega_arith))
    (fun i hi => hp6.al8 (by omega_arith) (by omega_arith)) c4 ((k6.gpr (by decide)).trans b3)
    ((k5.trans k6).gpr (by decide) |>.trans b0) hw (by omega_arith) (by unfold slot hdrBytes; omega_arith)
    (by omega_arith) (by omega_arith) hsep)
    fun u ⟨⟨_, _, cu, ou⟩, ku⟩ => ?_
  rw [hm6] at cu ou
  have wp3 : ∀ i < w, word v₃.mem P (8 * w + 8 * i) = word v.mem P (8 * w + 8 * i) := fun i hi =>
    Outside.word_sep o3 hsep (by omega_arith) (by omega_arith) hnp
  refine ⟨⟨fun i hi => by rw [cu i hi, wp3 i hi], fun i hi hi' => ?_,
    o3.trans (ou.mono (Nat.le_refl _) (by omega_arith)), ?_⟩, ?_⟩
  · exact (ou.word (Or.inr (by omega_arith)) (by omega_arith)).trans (z3 i hi')
  · rw [ku.gpr (by decide), (k5.trans k6).gpr (by decide), b0]
  · exact (k13.trans (k46.trans ku)).mono (by decide)

/-- `core`'s result, in a memory with the same first `n` words of `pre`. -/
theorem preOut_congr {nb : List Byte} {P : Addr} {n : Nat} {r : BitVec 64} {m m' : Mem}
    (h : ∀ i < n, Mont.word m' P (8 * i) = Mont.word m P (8 * i)) (hp : Pre.preOut nb P n r m) :
    Pre.preOut nb P n r m' := by
  unfold Pre.preOut at hp ⊢
  rw [wordsAt_eq h]
  exact hp

/-- The registers written up to `n`'s values. -/
def anRegs : List Reg := aRegs ++ nRegs ++ Pre.coreRegs ++ [.t3, .t0, .s0, .t4, .t5]

/-- What holds after `n`'s values and `R² mod n` in `X`'s array 6, from the
entry state `s₀`: as after the checks (`A`), `n`'s values in `pre`, and
`X`'s array 6 holding `R² mod n` under a set mask, zero-extended. -/
structure AN (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : Mont.word s.mem (cS s₀) oOut = s₀.gpr .a0
  hN : Mont.word s.mem (cS s₀) oN = s₀.gpr .a2
  hNL : Mont.word s.mem (cS s₀) oNLen = s₀.gpr .a3
  hPL : Mont.word s.mem (cS s₀) oPLen = s₀.gpr .a5
  hQL : Mont.word s.mem (cS s₀) oQLen = s₀.gpr .a7
  hBP : Mont.word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : Mont.word s.mem (cS s₀) oBQ =
    Mont.off (cS s₀) (slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)))
  hMask : Mont.word s.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  s6 : s.gpr .s6 = cS s₀
  s11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x4 : wordsVal s.mem (cS s₀) (slot (cwX s₀) 4) (cwX s₀) = if cb s₀ then cP s₀ else 3
  x5 : wordsVal s.mem (cS s₀) (slot (cwX s₀) 5) (cwX s₀) = if cb s₀ then cQ s₀ else 3
  out : ∃ r, Pre.preOut (nB s₀) (s₀.gpr .a0) (2 * cw s₀) r s.mem
  x6 : cb s₀ = true → wordsVal s.mem (cS s₀) (slot (cwX s₀) 6) (cw s₀) = 2 ^ (128 * cw s₀) % cN s₀
  x6z : ∀ i, cw s₀ ≤ i → i < cwX s₀ → Mont.word s.mem (cS s₀) (slot (cwX s₀) 6 + 8 * i) = 0
  keep : Keep anRegs s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

local macro "oa" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only
  [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith))

/-- After the checks, `n`'s values to `pre` and `R² mod n` into `X`'s array 6. -/
theorem partN_ok {s₀ t : State} (hP : PF s₀) (hA : A s₀ t) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ u, AN s₀ u → WP isa c u Q) :
    WP isa (.seq (.block PrivPre.setupN) (.seq Precompute.core (.seq PrivPre.xIn c))) t Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have hPS := hP.sepPre
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5; have eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7
  have eX8 := e (cwX s₀) 8; have eN0 := e (cw s₀) 0; have eN8 := e (cw s₀) 8
  have hh : hdrBytes = 256 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  refine WP.seq (WP.mono (setupN_ok hP hA) fun v ⟨⟨v5, v7, v8, v0, va7, va2, _, va6, vm⟩, kv⟩ => ?_)
  have kAv := hA.keep.trans kv
  have bN : Spec.Rsa.bytesAt v.mem (s₀.gpr .a2) (ck s₀) = nB s₀ := by
    rw [vm]
    exact bytes_frame hA.frame hP.dN (Nat.le_of_lt (BitVec.isLt _))
  refine WP.seq (WP.mono (Pre.core_ok (hA.scr.congr kv.2.2) (pre16 hP kAv.2.2) dw k64 k1024 (by oa) v5 v8
    v7 va7 va2 va6 v0 (by rw [kAv.2.1, kAv.2.2]; exact hP.rN) hP.sN (sep16 hP)) fun t₁ ⟨⟨tO, tF⟩, kt⟩ => ?_)
  rw [bN] at tO
  have kAt := kAv.trans kt
  have kvt := kv.trans kt
  have th : ∀ d, d + 8 ≤ 256 → Mont.word t₁.mem (cS s₀) d = Mont.word t.mem (cS s₀) d := fun d hd => by
    rw [core_word_hdr tF hPS (by oa) (by oa) (by oa) hn, vm]
  -- `X`'s words past `core`'s arrays.
  have tx : ∀ d, slot (cw s₀) 0 + 40 * (cw s₀ + 2) ≤ d → d + 8 ≤ cZ s₀ →
      Mont.word t₁.mem (cS s₀) d = Mont.word t.mem (cS s₀) d := fun d hd hd' => by
    rw [← vm]
    refine Mem.readW_congr fun i hi => tF _ fun r hr hc => ?_
    have hx := ofs_off' (cS s₀) (d := d) (i := i) (by oa)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := in_of_contains hc (by oa)
      oa
    · change (_ - s₀.gpr .a0).toNat + 1 ≤ 16 * cw s₀ at hc
      have := hPS (Mont.off (cS s₀) d + BitVec.ofNat 64 i)
        (by change (Mont.off (cS s₀) d + BitVec.ofNat 64 i - s₀.gpr .a0).toNat < _; oa)
      change _ ≤ (_ - cS s₀).toNat at this
      oa
  have t6 : t₁.gpr .s6 = cS s₀ := (kvt.gpr (by decide)).trans hA.s6
  have t11 : t₁.gpr .s11 = BitVec.ofNat 64 (8 * (2 * cw s₀ + 2)) := (kvt.gpr (by decide)).trans hA.s11
  have hst : Scr t₁ (cS s₀) (cZ s₀) := hA.scr.congr kvt.2.2
  -- `R² mod n` into `X`'s array 6.
  refine WP.seq (WP.mono (xIn_ok (w := cw s₀) hst (pre16 hP kAt.2.2)
    (fun x hx => hPS x (by oa)) (by oa) (by oa) t6 t11
    ((kt.gpr (by decide)).trans v0) ((kt.gpr (by decide)).trans v5) (by oa))
    fun u ⟨⟨c6, z6, o6, _⟩, ku⟩ => ?_)
  have hu : ∀ d, d + 8 ≤ slot (cwX s₀) 6 → Mont.word u.mem (cS s₀) d = Mont.word t₁.mem (cS s₀) d := fun d hd =>
    o6.word (Or.inl hd) (by oa)
  have hdr : ∀ d, d + 8 ≤ 256 → Mont.word u.mem (cS s₀) d = Mont.word t.mem (cS s₀) d := fun d hd => by
    rw [hu d (by oa), th d hd]
  have pu : ∀ i < 2 * cw s₀, Mont.word u.mem (s₀.gpr .a0) (8 * i) = Mont.word t₁.mem (s₀.gpr .a0) (8 * i) :=
    fun i hi => Outside.word_sep o6 (fun x hx => hPS x (by oa)) (by oa) (by oa) hnP
  have kall := kAt.trans ku
  have ktu := kvt.trans ku
  have hX : ∀ j, j = 4 ∨ j = 5 → wordsVal u.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) =
      wordsVal t.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) := fun j hj =>
    Win.wv_words fun i hi => by
      rw [hu _ (by rcases hj with rfl | rfl <;> omega_arith),
        tx _ (by rcases hj with rfl | rfl <;> omega_arith) (by rcases hj with rfl | rfl <;> omega_arith)]
  refine hc u ⟨hA.scr.congr (kv.trans (kt.trans ku)).2.2, by rw [hdr _ (by decide)]; exact hA.hOut,
    by rw [hdr _ (by decide)]; exact hA.hN, by rw [hdr _ (by decide)]; exact hA.hNL,
    by rw [hdr _ (by decide)]; exact hA.hPL, by rw [hdr _ (by decide)]; exact hA.hQL,
    by rw [hdr _ (by decide)]; exact hA.hBP, by rw [hdr _ (by decide)]; exact hA.hBQ,
    by rw [hdr _ (by decide)]; exact hA.hMask,
    (ktu.gpr (by decide)).trans hA.s6, (ktu.gpr (by decide)).trans hA.s11,
    by rw [hX 4 (by decide)]; exact hA.x4, by rw [hX 5 (by decide)]; exact hA.x5,
    ⟨t₁.gpr .a0, ?_⟩, fun hb => ?_, fun i hi hi' => z6 i hi hi',
    kall.mono fun _ h => by simp only [anRegs, List.append_assoc] at h ⊢; exact h, fun i hi => ?_, ?_⟩
  · exact preOut_congr pu tO
  · have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = true := by
      have := hb; simp only [cb, privMask, Bool.and_eq_true] at this; exact this.1
    have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
    unfold Pre.preOut at tO
    rw [VG.Proof.Bignum.publicPrecompute_some hlen hv] at tO
    obtain ⟨-, -, h2⟩ := VG.Proof.Bignum.pre_of_some hlen k64
      (by rw [VG.Proof.Bignum.publicPrecompute_some hlen hv, tO.2])
    rw [Win.wv_words fun i hi => c6 i hi, Pre.wordsVal_eq_wv]
    exact h2
  · have esav : off (savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := by
      simp only [off, savW]; rw [Offset.add_add]
    have h1 := hA.sav i hi
    rw [esav] at h1 ⊢
    change Mont.word u.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [hdr _ (by oa)]
    exact h1
  · have F1 : Frame [preR s₀, scrR s₀] v.mem t₁.mem := tF.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base _ (by oa)⟩
      · exact ⟨preR s₀, List.mem_cons_self .., sub_len (by oa)⟩
    have F2 : Frame [preR s₀, scrR s₀] t₁.mem u.mem := frame_of_outside o6 (by oa)
    rw [vm] at F1
    exact (hA.frame.trans F1).trans F2

end VG.Proof.Bignum.RISCV64.PrivPre
