module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on PPC64LE: the modulus's values first

`partN_ok`: after the checks (`A`), `n`'s values to `pre` (`setupN`,
`Precompute.core`, in the working space laid out for `w` words at `X`'s base,
which leaves `X`'s arrays 4 and 5 as they are), then `R² mod n` from `pre`
into `X`'s array 6, zero-extended to its `2 w` words (`xIn`), for the
factors' `R² mod p` (`AN`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- An address in the region at `B + o` of `n` bytes is at those offsets. -/
theorem in_of_contains {B y : Addr} {o n : Nat} (h : (⟨off B o, n⟩ : Region).Contains y 1) (ho : o < 2 ^ 64)
    (hn : B.toNat + o + n ≤ 2 ^ 64) : o ≤ ofs B y ∧ ofs B y < o + n := by
  simp only [Region.Contains, off] at h
  simp only [ofs]
  have e1 : (y - B).toNat = (2 ^ 64 - B.toNat + y.toNat) % 2 ^ 64 := BitVec.toNat_sub _ _
  have e2 : (y - (B + BitVec.ofNat 64 o)).toNat = (2 ^ 64 - (B.toNat + o) % 2 ^ 64 + y.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 from ho)]
  rw [e2] at h
  rw [e1]
  have := B.isLt; have := y.isLt
  omega_arith

/-- A load of the header's word at `o` (`r23`) into `rd`. -/
theorem ldH_ok {s : State} {S : Addr} {Z o : Nat} {rd : Reg} (hs : Scr s S Z) (h23 : s.gpr .r23 = S)
    (ho : o + 8 ≤ Z) (ho' : o < 2 ^ 15 ∧ o % 4 = 0) :
    WP isa (.block [.load .d rd .r23 o]) s fun t =>
      (t.gpr rd = word s.mem S o ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) ho' (by rw [h23]; exact hs.ld ho), Option.some.injEq,
    exists_eq_left', h23]
  exact ⟨⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩

/-- The registers `setupN` writes. -/
def nRegs : List Reg := [.r19, .r12, .r6, .r21, .r11, .r4, .r10, .r5, .r8, .r9]

/-- `setupN`, after the checks: `Precompute.core`'s registers. -/
theorem setupN_ok {s₀ u : State} (hP : PF s₀) (hB : A s₀ u) :
    WP isa (.block PrivPre.setupN) u fun v =>
      (v.gpr .r19 = s₀.gpr .r3 ∧ v.gpr .r12 = s₀.gpr .r5 ∧ v.gpr .r6 = BitVec.ofNat 64 (ck s₀) ∧
        v.gpr .r21 = cS s₀ ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧
        v.gpr .r10 = off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .r5 = off (cS s₀) (slot (cw s₀) 1) ∧
        v.gpr .r8 = off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .r9 = off (cS s₀) (slot (cw s₀) 3) ∧ v.mem = u.mem) ∧
      Keep nRegs u v := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  rw [show PrivPre.setupN = [.load .d .r19 .r23 oOut] ++ ([.load .d .r12 .r23 oN] ++ ([.load .d .r6 .r23 oNLen] ++
    [.addi .r21 .r23 0, .addi .r11 .r6 7, .lsr .d .r11 .r11 3, .lsl .r4 .r11 3, .addi .r4 .r4 16,
      .addi .r10 .r21 hdrBytes, .add .r5 .r10 .r4, .add .r8 .r5 .r4, .add .r9 .r8 .r4, .lsl .r11 .r11 1])) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok hB.scr hB.r23 (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oOut] at *; omega_arith) (by decide)) fun u1 ⟨⟨a19, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hB.scr.congr k1.wr) ((k1.gpr _ (by decide)).trans hB.r23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oN] at *; omega_arith) (by decide))
    fun u2 ⟨⟨a12, m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hB.scr.congr (k1.trans k2).wr) (((k1.trans k2).gpr _ (by decide)).trans hB.r23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oNLen] at *; omega_arith)
    (by decide)) fun u3 ⟨⟨a6, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have e6 : u3.gpr .r6 = BitVec.ofNat 64 K := by
    rw [a6, m2, m1, hB.hNL, ← hKe]; exact (ofNat_toNat64 _).symm
  have e23 : u3.gpr .r23 = cS s₀ := (k13.gpr _ (by decide)).trans hB.r23
  refine WP.mono (WP.keep [.r21, .r11, .r4, .r10, .r5, .r8, .r9]
    (Q := fun v => v.gpr .r21 = cS s₀ ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧
      v.gpr .r10 = off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .r5 = off (cS s₀) (slot (cw s₀) 1) ∧
      v.gpr .r8 = off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .r9 = off (cS s₀) (slot (cw s₀) 3) ∧ v.mem = u3.mem) (by
        prun [e6, e23, BitVec.add_zero, Pre.ofNat_add7_shr3 K (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith), Pre.ofNat_shl3, Pre.ofNat_shl1, hdrBytes]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat, cw, hKe] <;>
          (try congr 2) <;> omega_arith) (by decide))
    fun v ⟨⟨v21, v11, v10, v5, v8, v9, vm⟩, kv⟩ => ⟨⟨?_, ?_, ?_, v21, v11, v10, v5, v8, v9, by rw [vm, m3, m2, m1]⟩,
      (k13.trans kv).mono (by decide)⟩
  · rw [kv.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), a19, hB.hOut]
  · rw [kv.gpr _ (by decide), k3.gpr _ (by decide), a12, m1, hB.hN]
  · rw [kv.gpr _ (by decide), e6, hKe]

/-- A word of the header, after `core`. -/
theorem core_word_hdr {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : d + 8 ≤ hdrBytes) (hn : n ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64) (hL0 : 0 < L) :
    word m' S d = word m S d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx : ofs S (off S d + BitVec.ofNat 64 i) = d + i := by
    simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by unfold hdrBytes at hd; omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by unfold hdrBytes; omega_arith) (by omega_arith)
    omega_arith
  · simp only [Region.Contains] at hc
    have := hsep (off S d + BitVec.ofNat 64 i) (by simp only [ofs]; omega_arith)
    unfold hdrBytes at hd hZ
    omega_arith


local macro "oa" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only
  [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith))

/-- `pre`'s first `16 w` bytes, in a state with `s₀`'s writable regions. -/
theorem pre16 {s₀ s : State} (hP : PF s₀) (h : s.wr = s₀.wr) : Scr s (s₀.gpr .r3) (16 * cw s₀) := by
  have hpl := hP.preLen
  have hnP := hP.pre.nowrap
  exact ⟨let ⟨B0, o, L, hm, hb, hL, hL'⟩ := hP.pre.wr; ⟨B0, o, L, by rw [h]; exact hm, hb, by
      simp (config := { failIfUnchanged := false }) only [cw, ck, cpL, cqL] at *; omega_arith, hL'⟩,
      by simp (config := { failIfUnchanged := false }) only [cw, ck] at *; omega_arith⟩

/-- The working space is apart from `pre`'s first `16 w` bytes. -/
theorem sep16 {s₀ : State} (hP : PF s₀) : ∀ x, ofs (cS s₀) x < cZ s₀ → 16 * cw s₀ ≤ ofs (s₀.gpr .r3) x :=
  fun x hx => by
    have hpl := hP.preLen
    refine Nat.le_of_not_lt fun hc => ?_
    have := hP.sepPre x (by rw [hpl]; omega_arith)
    omega_arith


/-! ## `R² mod n` into `X`'s array 6 -/

theorem sub_len {P : Addr} {n k : Nat} (h : n ≤ k) : Region.Sub ⟨P, n⟩ ⟨P, k⟩ := fun _ hx => by
  simp only [Region.Contains] at hx ⊢; omega_arith


/-- `xIn`: `R² mod n` (`pre`'s words `w` to `2 w`, at `r19`) into `X`'s array 6
(at `r27`, `r28`), zero-extended to its `2 w` words, for `r11 = 2 w`. -/
theorem xIn_ok {v : State} {S P : Addr} {Z w : Nat} (hs : Scr v S Z) (hp : Scr v P (16 * w))
    (hsep : ∀ x, ofs P x < 16 * w → Z ≤ ofs S x) (hw : 1 ≤ w) (hw' : w < 2 ^ 29)
    (h27 : v.gpr .r27 = off S (slot (2 * w) 0)) (h28 : v.gpr .r28 = BitVec.ofNat 64 (8 * (2 * w + 2)))
    (h11 : v.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h19 : v.gpr .r19 = P) (hZ : slot (2 * w) 7 ≤ Z) :
    WP isa PrivPre.xIn v fun u =>
      ((∀ i < w, word u.mem S (slot (2 * w) 6 + 8 * i) = word v.mem P (8 * w + 8 * i)) ∧
        (∀ i, w ≤ i → i < 2 * w → word u.mem S (slot (2 * w) 6 + 8 * i) = 0) ∧
        Outside S (slot (2 * w) 6) (8 * (2 * w)) v.mem u.mem ∧ u.gpr .r11 = BitVec.ofNat 64 (2 * w)) ∧
      Keep [.r14, .r11, .r0, .r17, .r3, .r15] v u := by
  have hn := hs.nowrap
  have hnp := hp.nowrap
  have es : ∀ j, slot (2 * w) j = 256 + j * (8 * (2 * w + 2)) := fun _ => rfl
  have e6 := es 6; have e7 := es 7
  unfold PrivPre.xIn
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Crt.xb_ok (rd := .r14) (by decide) (by decide) h27 h28 6) fun v₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = BitVec.ofNat 64 (2 * (2 * w)) ∧ u.mem = v₁.mem)
    (by prun [(k1.gpr _ (by decide)).trans h11, Pre.ofNat_shl1]) (by decide)) fun v₂ ⟨⟨a11, m2⟩, k2⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr (k1.trans k2).wr) ((k2.gpr _ (by decide)).trans a14) a11
    (by omega_arith) (by omega_arith) (by omega_arith)) fun v₃ ⟨⟨_, z3, o3⟩, k3⟩ => ?_)
  have hm2 : v₂.mem = v.mem := by rw [m2, m1]
  rw [hm2] at o3
  have k13 := (k1.trans k2).trans k3
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ u.mem = v₃.mem)
    (by prun [(k3.gpr _ (by decide)).trans a11, Crt.shr1_ofNat (show 2 * w < 2 ^ 62 by omega_arith)]) (by decide))
    fun v₄ ⟨⟨b11, m4⟩, k4⟩ => ?_
  refine WP.mono (Crt.xb_ok (rd := .r14) (by decide) (by decide) (((k13.trans k4).gpr _ (by decide)).trans h27)
    (((k13.trans k4).gpr _ (by decide)).trans h28) 6) fun v₅ ⟨⟨b14, m5⟩, k5⟩ => ?_
  refine WP.mono (WP.keep [.r3, .r15] (Q := fun u => u.gpr .r15 = off P (8 * w) ∧ u.mem = v₅.mem)
    (by
      prun [(k5.gpr _ (by decide)).trans b11, ((k13.trans (k4.trans k5)).gpr _ (by decide)).trans h19]
      have e : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        omega_arith
      rw [e]) (by decide)) fun v₆ ⟨⟨c15, m6⟩, k6⟩ => ?_
  have k46 := (k4.trans k5).trans k6
  have hm6 : v₆.mem = v₃.mem := by rw [m6, m5, m4]
  have hp6 : Scr v₆ P (16 * w) := hp.congr (k13.trans k46).wr
  refine WP.mono (Pub.copyIn_ok (B := S) (P := P) (Zp := 16 * w) (dS := 8 * w) (dD := slot (2 * w) 6) (w := w)
    (hs.congr (k13.trans k46).wr) hnp (fun i hi => hp6.ld (by omega_arith)) c15 ((k6.gpr _ (by decide)).trans b14)
    ((k5.trans k6).gpr _ (by decide) |>.trans b11) hw (by omega_arith) (by omega_arith) (by omega_arith) hsep)
    fun u ⟨⟨_, _, cu, ou⟩, ku⟩ => ?_
  rw [hm6] at cu ou
  have wp3 : ∀ i < w, word v₃.mem P (8 * w + 8 * i) = word v.mem P (8 * w + 8 * i) := fun i hi =>
    Outside.word_sep o3 hsep (by omega_arith) (by omega_arith) hnp
  have o3' : Outside S (slot (2 * w) 6) (8 * (2 * w)) v.mem v₃.mem := fun x hx => o3 x hx
  have ou' : Outside S (slot (2 * w) 6) (8 * (2 * w)) v₃.mem u.mem := fun x hx => ou x (by
    simp only [VG.Proof.Bignum.ofs] at hx ⊢; omega_arith)
  refine ⟨⟨fun i hi => by rw [cu i hi, wp3 i hi], fun i hi hi' => ?_, o3'.trans ou', ?_⟩, ?_⟩
  · exact (ou.word (Or.inr (by omega_arith)) (by omega_arith)).trans (z3 i hi')
  · rw [ku.gpr _ (by decide), (k5.trans k6).gpr _ (by decide), b11]
  · exact (k13.trans (k46.trans ku)).mono (by decide)

/-- The registers written up to `n`'s values. -/
def anRegs : List Reg := aRegs ++ nRegs ++ Pre.coreRegs ++ [.r14, .r11, .r0, .r17, .r3, .r15]

/-- What holds after `n`'s values and `R² mod n` in `X`'s array 6, from the entry state `s₀`. -/
structure AN (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : word s.mem (cS s₀) oOut = s₀.gpr .r3
  hN : word s.mem (cS s₀) oN = s₀.gpr .r5
  hNL : word s.mem (cS s₀) oNLen = s₀.gpr .r6
  hPL : word s.mem (cS s₀) oPLen = s₀.gpr .r8
  hQL : word s.mem (cS s₀) oQLen = s₀.gpr .r10
  hBP : word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : word s.mem (cS s₀) oBQ = off (cS s₀) (slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 24)
  r23 : s.gpr .r23 = cS s₀
  r26 : s.gpr .r26 = Crt.bmask (cb s₀)
  r27 : s.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x4 : val32 s.mem (cS s₀) (slot (cwX s₀) 4) (2 * cwX s₀) = if cb s₀ then cP s₀ else 3
  x5 : val32 s.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = if cb s₀ then cQ s₀ else 3
  out : ∃ r, Pre.preOut (nB s₀) (s₀.gpr .r3) (2 * cw s₀) r s.mem
  x6 : cb s₀ = true → wv s.mem (cS s₀) (slot (cwX s₀) 6) (cw s₀) = 2 ^ (128 * cw s₀) % cN s₀
  x6z : ∀ i, cw s₀ ≤ i → i < cwX s₀ → word s.mem (cS s₀) (slot (cwX s₀) 6 + 8 * i) = 0
  keep : Keep anRegs s₀ s
  sav : ∀ i < 18, s.mem.readW (off (Crt.savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

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
  have dX : cwX s₀ = 2 * cw s₀ := rfl
  have es : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX4 := es (cwX s₀) 4; have eX5 := es (cwX s₀) 5; have eX6 := es (cwX s₀) 6; have eX8 := es (cwX s₀) 8
  refine WP.seq (WP.mono (setupN_ok hP hA) fun v ⟨⟨v19, v12, v6, v21, v11, v10, v5, v8, v9, vm⟩, kv⟩ => ?_)
  have kAv := hA.keep.trans kv
  have bN : Spec.Rsa.bytesAt v.mem (s₀.gpr .r5) (ck s₀) = nB s₀ := by
    rw [vm]
    exact bytes_frame hA.frame hP.dN (Nat.le_of_lt (BitVec.isLt _))
  refine WP.seq (WP.mono (Pre.core_ok (hA.scr.congr kv.wr) (pre16 hP kAv.wr) dw k64 k1024 (by oa) v19 v6 v12 v10
    v5 v8 v9 v11 v21 (by rw [kAv.rd, kAv.wr]; exact hP.rN) hP.sN (sep16 hP)) fun t₁ ⟨⟨tO, tF⟩, kt⟩ => ?_)
  rw [bN] at tO
  have kAt := kAv.trans kt
  have th : ∀ d, d + 8 ≤ 256 → word t₁.mem (cS s₀) d = word t.mem (cS s₀) d := fun d hd => by
    rw [core_word_hdr tF hPS hd (by rw [hpl]; omega_arith) (by oa) hn (by omega_arith), vm]
  -- `X`'s words past `core`'s arrays.
  have tx : ∀ d, slot (cw s₀) 0 + 32 * (cw s₀ + 2) ≤ d → d + 8 ≤ cZ s₀ →
      word t₁.mem (cS s₀) d = word t.mem (cS s₀) d := fun d hd hd' => by
    rw [← vm]
    refine Mem.readW_congr fun i hi => tF _ fun r hr hc => ?_
    have hx : ofs (cS s₀) (off (cS s₀) d + BitVec.ofNat 64 i) = d + i := by
      simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := in_of_contains hc (by unfold hdrBytes; omega_arith) (by unfold hdrBytes; oa)
      unfold slot hdrBytes at hd this; omega_arith
    · simp only [Region.Contains] at hc
      have := hPS (off (cS s₀) d + BitVec.ofNat 64 i) (by
        simp only [ofs] at hx ⊢; rw [hpl]; omega_arith)
      simp only [ofs] at hx this; omega_arith
  have kvt := kv.trans kt
  have t23 : t₁.gpr .r23 = cS s₀ := (kvt.gpr _ (by decide)).trans hA.r23
  have hst : Scr t₁ (cS s₀) (cZ s₀) := hA.scr.congr (kv.trans kt).wr
  -- `R² mod n` into `X`'s array 6.
  refine WP.seq (WP.mono (xIn_ok (w := cw s₀) hst (pre16 hP kAt.wr)
    (fun x hx => hPS x (by rw [hpl]; omega_arith)) (by oa) (by oa)
    ((kvt.gpr _ (by decide)).trans hA.r27) ((kvt.gpr _ (by decide)).trans hA.r28)
    ((kt.gpr _ (by decide)).trans v11) ((kt.gpr _ (by decide)).trans v19) (by oa))
    fun u ⟨⟨c6, z6, o6, _⟩, ku⟩ => ?_)
  have hu : ∀ d, d + 8 ≤ slot (cwX s₀) 6 → word u.mem (cS s₀) d = word t₁.mem (cS s₀) d := fun d hd =>
    o6.word (Or.inl hd) (by omega_arith)
  have hdr : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word t.mem (cS s₀) d := fun d hd => by
    rw [hu d (by omega_arith), th d hd]
  have pu : ∀ i < 2 * cw s₀, word u.mem (s₀.gpr .r3) (8 * i) = word t₁.mem (s₀.gpr .r3) (8 * i) := fun i hi =>
    Outside.word_sep o6 (fun x hx => hPS x (by rw [hpl]; omega_arith)) (by oa) (by omega_arith) hnP
  have kall := kAt.trans ku
  have ktu := kvt.trans ku
  have hX : ∀ j, j = 4 ∨ j = 5 → val32 u.mem (cS s₀) (slot (cwX s₀) j) (2 * cwX s₀) =
      val32 t.mem (cS s₀) (slot (cwX s₀) j) (2 * cwX s₀) := fun j hj => by
    rw [Pre.val32_eq_wv, Pre.val32_eq_wv]
    exact wv_congr fun i hi => by
      rw [hu _ (by rcases hj with rfl | rfl <;> omega_arith), tx _ (by rcases hj with rfl | rfl <;> oa)
        (by rcases hj with rfl | rfl <;> oa)]
  refine hc u ⟨hA.scr.congr (kv.trans (kt.trans ku)).wr, by rw [hdr _ (by decide)]; exact hA.hOut,
    by rw [hdr _ (by decide)]; exact hA.hN, by rw [hdr _ (by decide)]; exact hA.hNL,
    by rw [hdr _ (by decide)]; exact hA.hPL, by rw [hdr _ (by decide)]; exact hA.hQL,
    by rw [hdr _ (by decide)]; exact hA.hBP, by rw [hdr _ (by decide)]; exact hA.hBQ,
    (ktu.gpr _ (by decide)).trans hA.r23, (ktu.gpr _ (by decide)).trans hA.r26,
    (ktu.gpr _ (by decide)).trans hA.r27, (ktu.gpr _ (by decide)).trans hA.r28,
    by rw [hX 4 (by decide)]; exact hA.x4, by rw [hX 5 (by decide)]; exact hA.x5,
    ⟨t₁.gpr .r3, ?_⟩, fun hb => ?_, fun i hi hi' => z6 i hi hi', kall.mono (by decide +kernel), fun i hi => ?_, ?_⟩
  · unfold Pre.preOut at tO ⊢
    rw [show Spec.Rsa.wordsAt u.mem (s₀.gpr .r3) (2 * cw s₀) = Spec.Rsa.wordsAt t₁.mem (s₀.gpr .r3) (2 * cw s₀) from
      List.map_congr_left fun i hi => pu i (List.mem_range.mp hi)]
    exact tO
  · have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = true := by
      have := hb; simp only [cb, privMask, Bool.and_eq_true] at this; exact this.1
    have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
    unfold Pre.preOut at tO
    rw [VG.Proof.Bignum.publicPrecompute_some hlen hv] at tO
    obtain ⟨-, -, h2⟩ := VG.Proof.Bignum.pre_of_some hlen k64
      (by rw [VG.Proof.Bignum.publicPrecompute_some hlen hv, tO.2])
    have e6 : wv u.mem (cS s₀) (slot (2 * cw s₀) 6) (cw s₀) = wv t₁.mem (s₀.gpr .r3) (8 * cw s₀) (cw s₀) :=
      wv_congr2 fun i hi => c6 i hi
    exact e6.trans h2
  · have e : Mont.off (Crt.savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := by
      simp only [Mont.off, Crt.savW]; rw [Offset.add_add]
    have h1 := hA.sav i hi
    change u.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _
    change t.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _ at h1
    rw [e] at h1 ⊢
    change word u.mem (cS s₀) (112 + 8 * i) = _
    change word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [hdr _ (by omega_arith)]; exact h1
  · have F1 : Frame [preR s₀, scrR s₀] v.mem t₁.mem := tF.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base _ (by oa)⟩
      · exact ⟨preR s₀, List.mem_cons_self .., sub_len (by rw [hpl]; omega_arith)⟩
    have hon : slot (2 * cw s₀) 6 + 8 * (2 * cw s₀) ≤ cZ s₀ := by oa
    have F2 : Frame [preR s₀, scrR s₀] t₁.mem u.mem := fun x hx => o6 x (by
      have := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [Region.Contains, ofs, cS, cZ] at this hon ⊢
      omega_arith)
    rw [vm] at F1
    exact (hA.frame.trans F1).trans F2

end VG.Proof.Bignum.PPC64LE.PrivPre
