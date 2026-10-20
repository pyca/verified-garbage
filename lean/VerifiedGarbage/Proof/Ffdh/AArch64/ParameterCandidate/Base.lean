module

public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# An FFDH parameter candidate on AArch64: the public data, the entry

`PP`: what the candidate's run depends on, all of it public: the working
space, the arguments and the tape. `PArgs`: the header words holding the
arguments, which no piece changes (`PArgs.frm`, for any change within
`PMut` ranges). `PSt`: between the pieces, for a working space of `w`
words. `entry_ok`, `zeros_ok`, `lenCheck_ok`: the front, up to the check of
the tape's length (`Front`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The public data -/

/-- What the candidate depends on: the working space (`Z` bytes at `B`),
`out`, `used`, `bits`, the generator, and the tape at `rp`. -/
structure PP where
  B : Addr
  Z : Nat
  op : Addr
  up : Addr
  bits : Nat
  g : Nat
  rp : Addr
  r : List Byte

/-- `out_len`. -/
abbrev PP.L (p : PP) : Nat := (p.bits + 7) / 8

/-- The bounds. -/
structure PDims (p : PP) : Prop where
  b1 : 512 ≤ p.bits
  b2 : p.bits ≤ 8192
  g : p.g = 2 ∨ p.g = 5
  z : 128 * p.L + 256 ≤ p.Z
  rl : p.r.length < 2 ^ 64

/-- The header words holding the arguments. -/
structure PArgs (m : Mem) (p : PP) : Prop where
  out : word m p.B (8 * kOut) = p.op
  usedP : word m p.B (8 * kUsedP) = p.up
  len : word m p.B (8 * fLen) = BitVec.ofNat 64 p.L
  bits : word m p.B (8 * fBits) = BitVec.ofNat 64 p.bits
  gen : word m p.B (8 * fGen) = BitVec.ofNat 64 p.g
  rand : word m p.B (8 * kRand) = p.rp
  rlen : word m p.B (8 * kRandLen) = BitVec.ofNat 64 p.r.length

/-- A range apart from the header words `PArgs` keeps (16, 17, 19, 20, 21,
24 and 25). -/
def PMut (r : Nat × Nat) : Prop :=
  8 * 26 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 16 ∨ (8 * 18 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 19) ∨
    (8 * 22 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 24)

theorem PMut.ofSlot (w j n : Nat) : PMut (slot w j, n) := Or.inl (by unfold VG.Proof.Bignum.slot hdrBytes; omega)

/-- A header word other than those of `PArgs`. -/
theorem PMut.hdr {i : Nat} (h : i < 16 ∨ i = 18 ∨ i = 22 ∨ i = 23 ∨ 26 ≤ i) : PMut (8 * i, 8) := by
  unfold PMut; omega

theorem PArgs.frm {m m' : Mem} {p : PP} (h : PArgs m p) {rs : List (Nat × Nat)} (hf : Frm p.B rs m m')
    (hm : ∀ r ∈ rs, PMut r) : PArgs m' p := by
  have k : ∀ {i : Nat}, i = 16 ∨ i = 17 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 24 ∨ i = 25 →
      word m' p.B (8 * i) = word m p.B (8 * i) := fun hi =>
    hf.word_eq (fun r hr => by have := hm r hr; unfold PMut at this; omega) (by omega)
  exact ⟨(k (by decide)).trans h.out, (k (by decide)).trans h.usedP, (k (by decide)).trans h.len,
    (k (by decide)).trans h.bits, (k (by decide)).trans h.gen, (k (by decide)).trans h.rand,
    (k (by decide)).trans h.rlen⟩

/-- Between the pieces, with a working space of `w` words. -/
structure PSt (p : PP) (w : Nat) (s : State) : Prop where
  ws : Ws s p.B p.Z w
  args : PArgs s.mem p
  src : Src s p.B p.Z p.rp p.r
  ou : OutUp s p.B p.Z p.op p.up p.L
  dims : PDims p

/-- `PSt` survives a piece that keeps the working space and changes only
memory in it, within `PMut` ranges. -/
theorem PSt.step {p : PP} {w w' : Nat} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg} (h : PSt p w s)
    (hws : Ws t p.B p.Z w') (hf : Frm p.B rs s.mem t.mem) (hm : ∀ r ∈ rs, PMut r)
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (k : Keep regs s t) : PSt p w' t :=
  ⟨hws, h.args.frm hf hm, h.src.congrK (InScr.of_frm hf hZ) k, h.ou.congr k.wr, h.dims⟩

/-- The header and the buffers, without the working space's layout. -/
structure PH (p : PP) (s : State) : Prop where
  scr : Scr s p.B p.Z
  x0 : s.gpr .x0 = p.B
  args : PArgs s.mem p
  src : Src s p.B p.Z p.rp p.r
  ou : OutUp s p.B p.Z p.op p.up p.L
  dims : PDims p

theorem PSt.ph {p : PP} {w : Nat} {s : State} (h : PSt p w s) : PH p s :=
  ⟨h.ws.scr, h.ws.x0, h.args, h.src, h.ou, h.dims⟩

/-- `PH` survives a change within `PMut` ranges of the working space. -/
theorem PH.step {p : PP} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg} (h : PH p s)
    (hf : Frm p.B rs s.mem t.mem) (hm : ∀ r ∈ rs, PMut r) (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (k : Keep regs s t)
    (h0 : .x0 ∉ regs) : PH p t :=
  ⟨h.scr.congr k.wr, (k.gpr .x0 h0).trans h.x0, h.args.frm hf hm, h.src.congrK (InScr.of_frm hf hZ) k,
    h.ou.congr k.wr, h.dims⟩

theorem PSt.scr {p : PP} {w : Nat} {s : State} (h : PSt p w s) : Scr s p.B p.Z := h.ws.scr

theorem PSt.x0 {p : PP} {w : Nat} {s : State} (h : PSt p w s) : s.gpr .x0 = p.B := h.ws.x0

/-! ## The precondition -/

/-- The public data, from the state on entry. -/
def ppOf (s : State) : PP :=
  ⟨s.gpr .x7, (stackArg s 0).toNat * 8, s.gpr .x0, s.gpr .x2, (s.gpr .x3).toNat,
    ((s.gpr .x4).setWidth 32).toNat, s.gpr .x5, pcRand s⟩

/-- What `code` uses of its precondition. -/
structure PCtx (s : State) : Prop where
  dims : PDims (ppOf s)
  len : (s.gpr .x1).toNat = (ppOf s).L
  hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8)
  rsrc : Src s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x5) (pcRand s)
  ou : OutUp s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x0) (s.gpr .x2) (ppOf s).L
  dor : ∀ i < (s.gpr .x6).toNat, ∀ j < (ppOf s).L, s.gpr .x5 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j

theorem pctx_of {s : State} (h : pcPre s) : PCtx s := by
  simp only [pcPre] at h
  obtain ⟨hsp, hrd, hwr, dOu, dOr, dOs, dOa, dUr, dUs, dUa, drs, dsa, wO, wU, wR, wS, hb1, hb2, hk, hg, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hr := src_of_region (s := s) (B := s.gpr .x7) (Z := (stackArg s 0).toNat * 8) (by rw [hrd]; simp)
    (by omega_using []) drs
  have hL : (ppOf s).L = (s.gpr .x1).toNat := by simp only [ppOf, PP.L]; omega
  have ho : OutUp s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x0) (s.gpr .x2) (ppOf s).L := by
    rw [hL]
    refine ⟨⟨⟨s.gpr .x2, 8⟩, by rw [hwr]; simp, ?_⟩, fun b hb => out_scr dUs (contains_byte _ (by omega_using [hb]) (by omega_using [])),
      fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega_using [hj]) (by omega_using [])⟩,
      fun j hj => out_scr dOs (contains_byte _ (by omega_using [hj]) (by omega_using [])), fun j hj b hb he => ?_⟩
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []
    · exact dOu _ (contains_byte _ (by omega_using [hj]) (by omega_using []))
        (by rw [he]; exact contains_byte _ (by omega_using [hb]) (by omega_using []))
  refine ⟨⟨hb1, hb2, hg, by simp only [ppOf, PP.L]; omega, ?_⟩, hL.symm, hs, hr, ho, ?_⟩
  · simp only [ppOf, pcRand, bytesAt_length]; exact BitVec.isLt _
  · rw [hL]
    intro i hi j hj hh
    exact dOr _ (contains_byte (s.gpr .x0) (i := j) (by omega_using [hj]) (by omega_using []))
      (by rw [← hh]; exact contains_byte _ (by omega_using [hi]) (by omega_using []))

theorem pcRand_length (s : State) : (pcRand s).length = (s.gpr .x6).toNat := bytesAt_length _ _ _

/-! ## The entry -/

theorem zext32 (x : BitVec 64) :
    ((x.setWidth 32 + BitVec.ofNat 32 0).setWidth 64) = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The header after the entry's stores. -/
def entryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 : BitVec 64) : Mem :=
  ((((((((m.writeW (off B (8 * kOut)) v0).writeW (off B (8 * kLen)) v1).writeW (off B (8 * fLen)) v1).writeW
    (off B (8 * kUsed)) v1).writeW (off B (8 * kUsedP)) v2).writeW (off B (8 * fBits)) v3).writeW
    (off B (8 * fGen)) v4).writeW (off B (8 * kRand)) v5).writeW (off B (8 * kRandLen)) v6

/-- The header words the entry stores. -/
structure EArgs (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 : BitVec 64) : Prop where
  out : word m B (8 * kOut) = v0
  len : word m B (8 * kLen) = v1
  flen : word m B (8 * fLen) = v1
  used : word m B (8 * kUsed) = v1
  usedP : word m B (8 * kUsedP) = v2
  bits : word m B (8 * fBits) = v3
  gen : word m B (8 * fGen) = v4
  rand : word m B (8 * kRand) = v5
  rlen : word m B (8 * kRandLen) = v6

theorem entryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 : BitVec 64) :
    EArgs (entryMem m B v0 v1 v2 v3 v4 v5 v6) B v0 v1 v2 v3 v4 v5 v6 ∧
      Outside B 0 (8 * 32) m (entryMem m B v0 v1 v2 v3 v4 v5 v6) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> unfold entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- After the entry, from the state `s` on entry. -/
structure EntryPost (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x7
  args : EArgs t.mem (s.gpr .x7) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3)
    (BitVec.ofNat 64 ((s.gpr .x4).setWidth 32).toNat) (s.gpr .x5) (s.gpr .x6)
  out : Outside (s.gpr .x7) 0 (8 * 32) s.mem t.mem
  keep : Keep [.x0, .x4] s t

theorem entry_ok {s : State} (c : PCtx s) : WP isa (.block entry) s (EntryPost s) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.dims.z
  have hw : ∀ i < 32, InRegions s.wr (off (s.gpr .x7) (8 * i)) 8 := fun i hi => hs.st (by
    simp only [ppOf] at hZ; omega_using [hZ, hi])
  refine WP.mono (WP.keep [.x0, .x4] (Q := fun t => t.gpr .x0 = s.gpr .x7 ∧
      t.mem = entryMem s.mem (s.gpr .x7) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3)
        (BitVec.ofNat 64 ((s.gpr .x4).setWidth 32).toNat) (s.gpr .x5) (s.gpr .x6)) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  · unfold entry
    brun [exec_addImm_w (show 0 < 4096 by decide), zext32, hdr_enc (show kOut < 32 by decide),
      hdr_enc (show kLen < 32 by decide), hdr_enc (show fLen < 32 by decide), hdr_enc (show kUsed < 32 by decide),
      hdr_enc (show kUsedP < 32 by decide), hdr_enc (show fBits < 32 by decide), hdr_enc (show fGen < 32 by decide),
      hdr_enc (show kRand < 32 by decide), hdr_enc (show kRandLen < 32 by decide),
      hw kOut (by decide), hw kLen (by decide), hw fLen (by decide), hw kUsed (by decide), hw kUsedP (by decide),
      hw fBits (by decide), hw fGen (by decide), hw kRand (by decide), hw kRandLen (by decide)]
    rfl
  obtain ⟨hA, ho⟩ := entryMem_facts s.mem (s.gpr .x7) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3)
    (BitVec.ofNat 64 ((s.gpr .x4).setWidth 32).toNat) (s.gpr .x5) (s.gpr .x6)
  rw [← hm] at hA ho
  exact ⟨h0, hA, ho, k⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate
