module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.WWit
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.WRound
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# A candidate on RISC-V: the witnesses' loop

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{WLoad,WDraw,WLoop,WBody}.lean`),
over RISC-V's blinded loop (`Proof/MillerRabin/RISCV64/Blinded/Loop.lean`):
`millerRabin_ok`, from a prepared candidate `c` of `w` words (`KCtx`) and the
tape `r` at `R`, after the candidate's `8 w` octets, `Witness.millerRabin`
leaves in `hStat` and `hUsed` what `primalityTest c (r.drop (8 w))` says
(`MOut`): 0 if the tape ran out, else 1 (probably prime) or 2 (composite), and
the octets read. Witness by witness (`MrLoopAt` from offset `8 w`): each draw
is the next `8 w` octets (`load_ok`), its witness (`witness_ok`) and its round
(`round_ok`). `res_ok`: the test's result (`testResult`) from them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum
open VG.Impl.MillerRabin.RISCV64.Search (ldh sth hRand hRandLen hUsed hK hIdx hChecks hStat loadDraw tapeShort)
open VG.Impl.RsaKeyGen.RISCV64.Witness (hUni)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep Kept)
open VG.Proof.Bignum (slot Frm word off ofs writeW_outside word_writeW_self)
open VG.Spec.RsaKeyGen (Rand loop mrStep witnessBytes)
open VG.Proof.RsaKeyGen (MrLoopAt mrSB wit seg)

/-! ## What the loop writes, and what it reads -/

/-- The ranges of the working space the loop's loads, witnesses and counts
write: `hUni`, `hUsed` and `hStat`, `hIdx`, and arrays 3–6. -/
def kgR (w : Nat) : List (Nat × Nat) :=
  [(8 * hUni, 8), (8 * hUsed, 16), (8 * hIdx, 8), (slot w 3, 4 * (8 * (w + 2)))]

/-- The prepared candidate survives a change of memory within `kgR` that
keeps `t1`. -/
theorem Prep.ofKgR {s t : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (env : Env t B (8 * L) w)
    (ht1 : t.gpr .t1 = s.gpr .t1) (hf : Frm B (kgR w) s.mem t.mem) : Prep t B L w c := by
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := env.hZ
  have hnw := env.hs.nowrap
  refine h.keep env (h.t1_of ht1) (fun d hd => hf.word_eq ?_ (by
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega))
    (fun j hj => ?_)
  · intro r hr
    simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega
  · have hj27 : j ≤ 27 := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    have hb : slot w j + 8 * w ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_right (8 * (w + 2)) hj27
      simp only [slot, hdrBytes]
      omega
    simp only [A, Pre.wordsVal_eq_wv]
    refine hf.wv_eq (fun r hr => ?_) hb
    simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega

/-- A change within `kgR` keeps memory outside the working space. -/
theorem frame_of_kgR {B : Addr} {L w : Nat} {m m' : Mem} (hf : Frm B (kgR w) m m')
    (hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L) (rs : List Region) : Frame (⟨B, 8 * L⟩ :: rs) m m' := by
  intro x hx
  have hb := hx _ (List.mem_cons_self ..)
  simp only [Region.Contains, Nat.not_le] at hb
  refine hf x fun r hr => Or.inr ?_
  have hr' : r.1 + r.2 ≤ 8 * L := by
    simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega
  show r.1 + r.2 ≤ (x - B).toNat
  exact Nat.le_trans hr' (Nat.lt_succ_iff.mp hb)

/-- What the loop reads and never writes: the prepared candidate `c` of `w`
words, the tape at `R` (`rl` octets, readable, apart from the working space
and the round's stack), the stack pointer (aligned, the round's 96 bytes
below it apart from the working space), and in the header a witness's octets
`8 w` and the uniform witnesses needed `ch`. -/
structure KCtx (s : State) (B : Addr) (L w c : Nat) (R : Addr) (rl ch : Nat) : Prop where
  prep : Prep s B L w c
  rand : word s.mem B (8 * hRand) = R
  randLen : word s.mem B (8 * hRandLen) = BitVec.ofNat 64 rl
  k : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)
  checks : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  cb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w
  ch63 : ch < 2 ^ 63
  rl64 : rl < 2 ^ 64
  rdR : ∀ i < rl, InRegions (s.rd ++ s.wr) (R + BitVec.ofNat 64 i) 1
  sepR : ∀ i < rl, ∀ x, ofs B x < 8 * L → R + BitVec.ofNat 64 i ≠ x
  sp16 : s.sp.toNat % 16 = 0
  sp : 96 ≤ s.sp.toNat
  stk : (below s.sp 96).Disjoint ⟨B, 8 * L⟩
  stkR : ∀ i < rl, ¬ (below s.sp 96).Contains (R + BitVec.ofNat 64 i) 1

/-- A witness's octets: `8 w`. -/
theorem KCtx.wb {s : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch) :
    witnessBytes c = 8 * w := by
  have hw4 := h.prep.env.hw
  have e := VG.Proof.MillerRabin.RISCV64.Blinded.witnessBytes_eq (c := c) (t := w - 1) (b := 64)
    (by rw [h.cb]; omega_arith) (by decide) (by decide)
  rw [e]; omega_arith

/-- `KCtx` in another state: the same prepared candidate, header words,
regions and stack pointer. -/
theorem KCtx.keep {s t : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch)
    (prep : Prep t B L w c)
    (hw : ∀ d, (d = 8 * hRand ∨ d = 8 * hRandLen ∨ d = 8 * hK ∨ d = 8 * hChecks) →
      word t.mem B d = word s.mem B d)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : KCtx t B L w c R rl ch :=
  ⟨prep, (hw _ (by simp)).trans h.rand, (hw _ (by simp)).trans h.randLen, (hw _ (by simp)).trans h.k,
    (hw _ (by simp)).trans h.checks, h.cb, h.ch63, h.rl64, by rw [rd, wr]; exact h.rdR, h.sepR,
    by rw [sp]; exact h.sp16, by rw [sp]; exact h.sp, by rw [sp]; exact h.stk, by rw [sp]; exact h.stkR⟩

/-- A change within `kgR` that keeps `t1` keeps `KCtx`. -/
theorem KCtx.ofKgR {s t : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch)
    (env : Env t B (8 * L) w) (ht1 : t.gpr .t1 = s.gpr .t1) (hf : Frm B (kgR w) s.mem t.mem)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : KCtx t B L w c R rl ch := by
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := env.hZ
  have hnw := env.hs.nowrap
  refine h.keep (Prep.ofKgR h.prep env ht1 hf) (fun d hd => hf.word_eq (fun r hr => ?_) ?_) rd wr sp
  · simp only [kgR, hUni, hUsed, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hRand, hRandLen, hK, hChecks] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes] <;> omega
  · simp only [hRand, hRandLen, hK, hChecks] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> omega

/-- The tape survives a change of memory within the working space and the
round's stack. -/
theorem KCtx.bytes_frame {s : State} {B R : Addr} {L w c rl ch : Nat} (h : KCtx s B L w c R rl ch)
    {m m' : Mem} (F : Frame [⟨B, 8 * L⟩, below s.sp 96] m m') :
    Spec.Rsa.bytesAt m' R rl = Spec.Rsa.bytesAt m R rl := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  refine F _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := Nat.le_of_not_lt fun hlt => h.sepR i hi _ hlt rfl
    change 8 * L ≤ (R + BitVec.ofNat 64 i - B).toNat at this
    simp only [Region.Contains]
    omega_arith
  · exact h.stkR i hi

/-! ## A draw's octets -/

/-- The registers `loadDraw` writes. -/
def kLoadRegs : List Reg := [.s7, .t2, .s8, .a7, .a0, .s0, .t3, .t4, .t5]

/-- The tape's address at `used` (`s7`), `hUsed := used + 8 w`, `8 w` in `s8`
and array 4's base in `a7`. -/
theorem loadA_ok {s : State} {B R : Addr} {L w c rl ch used : Nat} (h : KCtx s B L w c R rl ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) :
    WP isa (.block ([ldh .s7 hRand, ldh .t2 hUsed, .add .s7 .s7 .t2, ldh .s8 hK, .add .t2 .t2 .s8,
        sth .t2 hUsed] ++ VG.Impl.Bignum.RISCV64.PublicChecked.base .a7 4)) s fun u =>
      (u.gpr .s7 = R + BitVec.ofNat 64 used ∧ u.gpr .s8 = BitVec.ofNat 64 (8 * w) ∧
        u.gpr .a7 = off B (slot w 4) ∧
        u.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * w))) ∧
      Keep [.s7, .t2, .s8, .a7] s u := by
  have e := h.prep.env
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (u₁ : State) => (u₁.gpr .s7 = R + BitVec.ofNat 64 used ∧
      u₁.gpr .s8 = BitVec.ofNat 64 (8 * w) ∧
      u₁.mem = s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (used + 8 * w))) ∧
      Keep [.s7, .t2, .s8] s u₁) (WP.keep _ ?_ (by rfl) (by rfl)) fun u₁ ⟨⟨a7', a8, am⟩, k1⟩ => ?_
  · have r136 : s.mem.readW (B + 136#64) 64 = R := h.rand
    have r152 : s.mem.readW (B + 152#64) 64 = BitVec.ofNat 64 used := hu
    have r216 : s.mem.readW (B + 216#64) 64 = BitVec.ofNat 64 (8 * w) := h.k
    simp only [ldh, sth, hRand, hUsed, hK]
    brun [e.s6, hs.ld (d := 136) (n := 8) (by omega), hs.al8 (d := 136) (by omega) (by decide),
      hs.ld (d := 152) (n := 8) (by omega), hs.al8 (d := 152) (by omega) (by decide),
      hs.ld (d := 216) (n := 8) (by omega), hs.al8 (d := 216) (by omega) (by decide),
      hs.st (d := 152) (n := 8) (by omega), r136, r152, r216]
    rw [← BitVec.ofNat_add]
  · have e1 : Env u₁ B (8 * L) w := e.keep k1 (by decide)
    refine WP.mono (e1.base (rd := .a7) (by decide) 4) fun u₂ ⟨⟨b7, bm⟩, k2⟩ => ?_
    exact ⟨(k2.gpr (by decide)).trans a7', (k2.gpr (by decide)).trans a8, b7, bm.trans am⟩

/-- A draw from `used`: the next `8 w` octets of the tape into array 4,
`hUsed := used + 8 w`, and `a7` back at array 0. -/
theorem load_ok {s : State} {B R : Addr} {L w c rl ch used : Nat} (h : KCtx s B L w c R rl ch)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 used) (hav : used + 8 * w ≤ rl) :
    WP isa loadDraw s fun s' =>
      (A s'.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * w)) ∧
        word s'.mem B (8 * hUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
        Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem s'.mem ∧ s'.gpr .a7 = off B (slot w 0)) ∧
      Keep kLoadRegs s s' := by
  have e := h.prep.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  unfold loadDraw
  -- The tape's address, `hUsed`, and array 4's base.
  refine WP.seq (WP.mono (loadA_ok h hu) fun u ⟨⟨u7, u8, ua7, um⟩, ku⟩ => ?_)
  have hu' : Scr u B (8 * L) := hs.congr ku.2.2
  have hNr : ∀ i < 8 * w, InRegions (u.rd ++ u.wr) (off (R + BitVec.ofNat 64 used) i) 1 := fun i hi => by
    rw [ku.2.1, ku.2.2, show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.rdR _ (by omega)
  have hNs : ∀ i < 8 * w, ∀ x, ofs B x < 8 * L → off (R + BitVec.ofNat 64 used) i ≠ x := fun i hi x hx => by
    rw [show off (R + BitVec.ofNat 64 used) i = R + BitVec.ofNat 64 used + BitVec.ofNat 64 i from rfl,
      Offset.add_add]; exact h.sepR _ (by omega) x hx
  refine WP.seq (WP.mono (loadN_ok (k := 8 * w) hu' ua7
    (by rw [u7]; exact (BitVec.add_zero _).symm) u8 ((ku.gpr (by decide)).trans e.t0) (by omega) (Nat.le_refl _)
    (by omega) (by simp only [slot, hdrBytes]; omega) (by simp only [slot, hdrBytes]; omega)
    (by simp only [slot, hdrBytes]; omega) hNr hNs)
    fun v ⟨vv, vo, kv⟩ => ?_)
  -- The memory so far: `hUsed` and array 4.
  have fu : Frm B [(8 * hUsed, 8), (slot w 4, 8 * (w + 2))] s.mem v.mem := by
    refine Frm.trans (Frm.of_outside (o := 8 * hUsed) (n := 8) ?_ (by simp))
      (Frm.of_outside (o := slot w 4) (n := 8 * (w + 2))
        (fun x hx => vo x (by simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at hx ⊢; omega)) (by simp))
    rw [um]; exact writeW_outside _ _ _ (by simp only [hUsed]; omega)
  have bytes : Spec.Rsa.bytesAt u.mem (R + BitVec.ofNat 64 used) (8 * w) =
      Spec.Rsa.bytesAt s.mem (R + BitVec.ofNat 64 used) (8 * w) := by
    rw [um]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    rw [Offset.add_add]
    refine writeW_outside _ _ _ (by simp only [hUsed]; omega) _ ?_
    have := Nat.le_of_not_lt fun hlt => h.sepR (used + i) (by omega) _ hlt rfl
    simp only [hUsed]; omega
  have kvu := ku.trans kv
  have v6 : v.gpr .s6 = B := (kvu.gpr (by decide)).trans e.s6
  -- `a7` back.
  refine WP.mono (WP.keep [.a7] (Q := fun (y : State) => y.gpr .a7 = off B (slot w 0) ∧ y.mem = v.mem)
      (by brun [v6, hdrBytes]; simp only [slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by rfl) (by rfl))
    fun y ⟨⟨y7, ym⟩, ky⟩ => ?_
  refine ⟨⟨?_, ?_, by rw [ym]; exact fu, y7⟩, (kvu.trans ky).mono (by decide)⟩
  · simp only [A]
    rw [ym, vv, bytes]
  · have hv1 : word v.mem B (8 * hUsed) = word u.mem B (8 * hUsed) :=
      vo.word (by simp only [hUsed, slot, hdrBytes]; omega) (by simp only [hUsed]; omega)
    rw [ym, hv1, um]
    exact word_writeW_self _ _ _ _

/-! ## The loop's state -/

/-- What every state the loop reaches keeps from its entry `σ`. -/
structure LKeep (σ s : State) (B : Addr) (L w c : Nat) : Prop where
  prep : Prep s B L w c
  frame : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  s11 : s.gpr .s11 = σ.gpr .s11

/-- The loop after `k` witnesses passed, with `n + 1` iterations left, from
the entry state `σ`: the `k`-th witness is drawn at offset `8 w + 8 w k`. -/
structure LInv (σ s : State) (B R : Addr) (L w c rl ch : Nat) (r : Rand) (k n : Nat) : Prop where
  ctx : KCtx s B L w c R rl ch
  used : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w + 8 * w * k)
  idx : word s.mem B (8 * hIdx) = BitVec.ofNat 64 (k + 1)
  uni : word s.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * w) (8 * w) r k).2
  stat : word s.mem B (8 * hStat) = BitVec.ofNat 64 4
  tape : Spec.Rsa.bytesAt s.mem R rl = r
  frame : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  s11 : s.gpr .s11 = σ.gpr .s11
  mr : MrLoopAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) (8 * w) r k n

theorem LInv.keep {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n) : LKeep σ s B L w c :=
  ⟨h.ctx.prep, h.frame, h.sp, h.rd, h.wr, h.s11⟩

/-- `LKeep` through a step within `kgR` that keeps the registers it reads. -/
theorem LKeep.ofKgR {σ s t : State} {B : Addr} {L w c : Nat} {rs : List Reg} (h : LKeep σ s B L w c)
    (k : Keep rs s t) (hf : Frm B (kgR w) s.mem t.mem) (sp : t.sp = s.sp)
    (he : ∀ r ∈ VG.Proof.MillerRabin.RISCV64.envRegs, r ∉ rs := by decide) (h1 : Reg.t1 ∉ rs := by decide)
    (h11 : Reg.s11 ∉ rs := by decide) : LKeep σ t B L w c :=
  ⟨Prep.ofKgR h.prep (h.prep.env.keep k he) (k.gpr h1) hf, h.frame.trans (frame_of_kgR hf h.prep.env.hZ _),
    sp.trans h.sp, k.2.1.trans h.rd, k.2.2.trans h.wr, (k.gpr h11).trans h.s11⟩

/-- `LInv` through a step that keeps memory and the registers it reads. -/
theorem LInv.ofMem {σ s t : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat} {rs : List Reg}
    (h : LInv σ s B R L w c rl ch r k n) (hm : t.mem = s.mem) (k' : Keep rs s t) (sp : t.sp = s.sp)
    (he : ∀ r ∈ VG.Proof.MillerRabin.RISCV64.envRegs, r ∉ rs := by decide) (h1 : Reg.t1 ∉ rs := by decide)
    (h11 : Reg.s11 ∉ rs := by decide) : LInv σ t B R L w c rl ch r k n :=
  ⟨h.ctx.ofKgR (h.ctx.prep.env.keep k' he) (k'.gpr h1) (by rw [hm]; exact Frm.refl _ _ _) k'.2.1 k'.2.2 sp,
    by rw [hm]; exact h.used, by rw [hm]; exact h.idx, by rw [hm]; exact h.uni, by rw [hm]; exact h.stat,
    by rw [hm]; exact h.tape, by rw [hm]; exact h.frame, sp.trans h.sp, k'.2.1.trans h.rd, k'.2.2.trans h.wr,
    (k'.gpr h11).trans h.s11, h.mr⟩

/-- `RKept` for a range outside the round's and `hStat`, `hIdx`, by `omega` on
its offsets. -/
syntax "rkept_tac" : tactic
macro_rules
  | `(tactic| rkept_tac) => `(tactic| (
      intro i h1 h2
      simp only [RKept, Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        at h1 h2 ⊢
      and_intros <;> omega_arith))

/-- The outcome of one draw from `k` witnesses: composite or probably prime
(with the loop's result), or one more witness and the loop goes on. -/
def DOut (σ s : State) (B R : Addr) (L w c rl ch : Nat) (r : Rand) (k n : Nat) : Prop :=
  LKeep σ s B L w c ∧ word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w + 8 * w * (k + 1)) ∧
    ((n = 0 ∧ word s.mem B (8 * hStat) = BitVec.ofNat 64 2 ∧
        loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w)) =
          some (false, r.drop (8 * w + 8 * w * (k + 1)))) ∨
      (n = 0 ∧ word s.mem B (8 * hStat) = BitVec.ofNat 64 1 ∧
        loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w)) =
          some (true, r.drop (8 * w + 8 * w * (k + 1)))) ∨
      (0 < n ∧ LInv σ s B R L w c rl ch r (k + 1) (n - 1)))

/-! ## A draw -/

/-- One draw: its octets, its witness, its round and the outcome. -/
theorem draw_ok (Ri : RoundImpl) {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n) (hav : 8 * w + 8 * w * k + 8 * w ≤ rl) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.draw Ri.name Ri.code) s fun s' =>
      DOut σ s' B R L w c rl ch r k n := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hnw := e.hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hwb := ctx.wb
  have hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hk8 : 8 * k ≤ 8 * w * k := Nat.mul_le_mul_right k (by omega_arith)
  have hrl64 := ctx.rl64
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.draw
  -- The draw's octets.
  refine WP.seq (WP.mono (WP.rdwr (load_ok ctx h.used hav)) fun s1 ⟨⟨⟨v1, u1, f1, a71⟩, k1⟩, rd1, wr1, sp1⟩ => ?_)
  have f1' : Frm B (kgR w) s.mem s1.mem := VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen f1 (by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨(8 * hUsed, 16), by simp [kgR], Nat.le_refl _, by omega_arith⟩
    · exact ⟨(slot w 3, 4 * (8 * (w + 2))), by simp [kgR], by rw [es, es]; omega_arith, by rw [es, es]; omega_arith⟩)
  have e1 : Env s1 B (8 * L) w := ⟨e.hs.congr k1.2.2, a71, (k1.gpr (by decide)).trans e.s5,
    (k1.gpr (by decide)).trans e.t0, (k1.gpr (by decide)).trans e.s6, e.hw, e.hw', e.hZ⟩
  have p1 : Prep s1 B L w c := Prep.ofKgR ctx.prep e1 (k1.gpr (by decide)) f1'
  have hx1 : A s1.mem B w 4 = Spec.Rsa.os2ip (seg r (8 * w + 8 * w * k) (8 * w)) := by
    rw [v1, ← h.tape, VG.Proof.RsaKeyGen.seg_bytesAt s.mem R hav]
  -- Words a step keeps.
  have w1 : ∀ d, d + 8 ≤ 256 → d ≠ 8 * hUsed → d % 8 = 0 → word s1.mem B d = word s.mem B d := fun d hd hn h8 =>
    f1.word_eq (fun q hq => by
      simp only [hUsed, List.mem_cons, List.not_mem_nil, or_false] at hq hn
      rcases hq with rfl | rfl <;> simp only [es] <;> omega_arith) (by omega_arith)
  have u1' : word s1.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * w) (8 * w) r k).2 :=
    (w1 _ (by simp only [hUni]; omega_arith) (by simp [hUni, hUsed]) (by simp [hUni])).trans h.uni
  -- The witness.
  refine WP.seq (WP.mono (WP.rdwr (witness_ok (mctx_of e1 p1.t1 p1.n) e1.s6 ctx.prep.odd ctx.cb u1'))
    fun s2 ⟨⟨⟨a42, u2, f2⟩, k2⟩, rd2, wr2, sp2⟩ => ?_)
  rw [hx1] at a42 u2
  change A s2.mem B w 4 = (wit c (8 * w) r (8 * w + 8 * w * k)).1 at a42
  change word s2.mem B (8 * hUni) = BitVec.ofNat 64 ((mrSB c (8 * w) (8 * w) r k).2 +
    if (wit c (8 * w) r (8 * w + 8 * w * k)).2 then 1 else 0) at u2
  have e2 : Env s2 B (8 * L) w := e1.keep k2 (by decide)
  have f12 : Frm B (kgR w) s.mem s2.mem := f1'.trans (VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen f2 (by
    intro q hq
    simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [kgR], Nat.le_refl _, Nat.le_refl _⟩
    all_goals exact ⟨(slot w 3, 4 * (8 * (w + 2))), by simp [kgR], by (try rw [es, es]); (try dsimp only); omega_arith,
      by (try rw [es, es]); (try dsimp only); omega_arith⟩))
  have t12 : s2.gpr .t1 = s.gpr .t1 := (k2.gpr (by decide)).trans (k1.gpr (by decide))
  have p2 : Prep s2 B L w c := Prep.ofKgR ctx.prep e2 t12 f12
  have w2 : ∀ d, d + 8 ≤ 256 → d ≠ 8 * hUsed → d ≠ 8 * hUni → d % 8 = 0 →
      word s2.mem B d = word s.mem B d := fun d hd hn hn' h8 =>
    (f2.word_eq (fun q hq => by
      simp only [witRanges, hUni, List.mem_cons, List.not_mem_nil, or_false] at hq hn'
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [es] <;> omega_arith) (by omega_arith)).trans (w1 d hd hn h8)
  have sp12 : s2.sp = s.sp := sp2.trans sp1
  have hac : (wit c (8 * w) r (8 * w + 8 * w * k)).1 < c :=
    VG.Proof.MillerRabin.RISCV64.Blinded.witness_lt ctx.cb (by omega_arith)
  have hk63 : k + 1 + 1 < 2 ^ 63 := by omega_arith
  have hUle : (mrSB c (8 * w) (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w + 8 * w * k)).2 then 1 else 0) < 2 ^ 63 := by
    have := VG.Proof.RsaKeyGen.mrSB_uniform_le c (8 * w) (8 * w) r k
    split <;> omega_arith
  -- The round and its outcome.
  refine WP.mono (round_ok Ri p2 a42 hac (by rw [sp12]; exact ctx.sp16) (by rw [sp12]; exact ctx.sp)
    (by rw [sp12]; exact ctx.stk)
    ((w2 _ (by simp only [hIdx]; omega_arith) (by simp [hIdx, hUsed]) (by simp [hIdx, hUni]) (by simp [hIdx])).trans h.idx)
    u2 ((w2 _ (by simp only [hChecks]; omega_arith) (by simp [hChecks, hUsed]) (by simp [hChecks, hUni])
      (by simp [hChecks])).trans ctx.checks) hk63 hUle ctx.ch63) fun s3 h3 => ?_
  have hL8 : 256 ≤ 8 * L := by omega_arith
  have used3 : word s3.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w + 8 * w * (k + 1)) := by
    rw [h3.word (by simp only [hUsed]; omega_arith) (by simp only [hUsed]; rkept_tac)]
    rw [f2.word_eq (fun q hq => by
      simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [hUni, hUsed, es] <;> omega_arith)
      (by simp only [hUsed]; omega_arith), u1]
    exact congrArg _ (by rw [Nat.mul_succ]; omega_arith)
  have hUeq : (mrSB c (8 * w) (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w + 8 * w * k)).2 then 1 else 0) =
      (mrSB c (8 * w) (8 * w) r (k + 1)).2 := by
    rw [VG.Proof.RsaKeyGen.mrSB_uniform_next]
    cases (wit c (8 * w) r (8 * w + 8 * w * k)).2 <;> rfl
  have uni3 : word s3.mem B (8 * hUni) = BitVec.ofNat 64 (mrSB c (8 * w) (8 * w) r (k + 1)).2 := by
    rw [h3.word (by simp only [hUni]; omega_arith) (by simp only [hUni]; rkept_tac), u2, hUeq]
  have frame3 : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s3.mem := by
    refine h.frame.trans ((frame_of_kgR f12 hZ _).trans ?_)
    have := h3.frame
    rwa [sp12, h.sp] at this
  have sp3 : s3.sp = σ.sp := (h3.sp.trans sp12).trans h.sp
  have rd3 : s3.rd = σ.rd := ((h3.rd.trans rd2).trans rd1).trans h.rd
  have wr3 : s3.wr = σ.wr := ((h3.wr.trans wr2).trans wr1).trans h.wr
  have s113 : s3.gpr .s11 = σ.gpr .s11 :=
    (((h3.cs .s11 (by decide) (by decide) (by decide)).trans (k2.gpr (by decide))).trans (k1.gpr (by decide))).trans h.s11
  have lk : LKeep σ s3 B L w c := ⟨h3.prep, frame3, sp3, rd3, wr3, s113⟩
  have hav' : 8 * w + 8 * w * k + 8 * w ≤ r.length := by rw [hrl]; exact hav
  have hD : 8 * w + 8 * w * k + 8 * w = 8 * w + 8 * w * (k + 1) := by rw [Nat.mul_succ]; omega_arith
  have hround : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w + 8 * w * k)).1 =
      Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
        (wit c (8 * w) r (8 * w + 8 * w * k)).1 := rfl
  have st3 := h3.stat
  have id3 := h3.idx
  cases hr : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w + 8 * w * k)).1
  · -- The witness proves `c` composite.
    rw [hr] at hround st3
    obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_fail h.mr hwb (by omega_arith) hav' hround.symm
    rw [hD] at hl
    exact ⟨lk, used3, .inl ⟨hn0, st3, hl⟩⟩
  · rw [hr] at hround st3 id3
    simp only [↓reduceIte] at st3 id3
    rw [hUeq] at st3
    have hfirst := VG.Proof.RsaKeyGen.mrSB_first c (8 * w) (8 * w) r (k + 1)
    by_cases hd : 17 ≤ k + 1 + 1 ∧ ch ≤ (mrSB c (8 * w) (8 * w) r (k + 1)).2
    · have hg : ¬ VG.Proof.RsaKeyGen.goS ch (mrSB c (8 * w) (8 * w) r (k + 1)) := by
        unfold VG.Proof.RsaKeyGen.goS Spec.RsaKeyGen.blindedChecks
        omega_arith
      obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_done h.mr hwb (by omega_arith) hav' hround.symm hg
      rw [hD] at hl
      exact ⟨lk, used3, .inr (.inl ⟨hn0, by rw [st3]; simp only [statOf, hd, and_self, ↓reduceIte], hl⟩)⟩
    · have hg : VG.Proof.RsaKeyGen.goS ch (mrSB c (8 * w) (8 * w) r (k + 1)) := by
        unfold VG.Proof.RsaKeyGen.goS Spec.RsaKeyGen.blindedChecks
        omega_arith
      obtain ⟨hn, mr'⟩ := VG.Proof.RsaKeyGen.mrLoopAt_next h.mr hwb (by omega_arith) hav' hround.symm hg
      have w3 : ∀ d, (d = 8 * hRand ∨ d = 8 * hRandLen ∨ d = 8 * hK ∨ d = 8 * hChecks) →
          word s3.mem B d = word s.mem B d := fun d hd' => by
        simp only [hRand, hRandLen, hK, hChecks] at hd'
        rcases hd' with rfl | rfl | rfl | rfl <;>
          (rw [h3.word (by omega_arith) (by rkept_tac)]
           exact w2 _ (by omega_arith) (by simp [hUsed]) (by simp [hUni]) (by omega_arith))
      have ctx3 : KCtx s3 B L w c R rl ch := ctx.keep h3.prep w3 (h3.rd.trans (rd2.trans rd1))
        (h3.wr.trans (wr2.trans wr1)) (h3.sp.trans sp12)
      have tape3 : Spec.Rsa.bytesAt s3.mem R rl = r := by
        have b3 := ctx.bytes_frame (m := σ.mem) (m' := s3.mem) (by rw [h.sp]; exact frame3)
        have b0 := ctx.bytes_frame (m := σ.mem) (m' := s.mem) (by rw [h.sp]; exact h.frame)
        rw [b3, ← b0, h.tape]
      exact ⟨lk, used3, .inr (.inr ⟨hn, ⟨ctx3, used3, id3, uni3,
        by rw [st3]; simp only [statOf, hd, ↓reduceIte], tape3, frame3, sp3, rd3, wr3, s113, mr'⟩⟩)⟩

/-! ## The loop -/

/-- What the loop leaves: what `primalityTest c (r.drop (8 w))` says, in
`hStat` and, unless the tape ran out, `hUsed`. -/
def MOut (σ s : State) (B : Addr) (L w c rl : Nat) (r : Rand) : Prop :=
  LKeep σ s B L w c ∧
    match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
    | none => word s.mem B (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word s.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word s.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)

/-- The loop's check: `t4 :=` 1 if fewer than a draw's octets are left, else 0. -/
theorem check_ok {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n) :
    WP isa (.block tapeShort) s
      fun u => ((u.gpr .t4 = BitVec.ofNat 64 (if rl - (8 * w + 8 * w * k) < 8 * w then 1 else 0) ∧
        u.mem = s.mem ∧ u.sp = s.sp) ∧ u.rd = s.rd ∧ u.wr = s.wr) ∧ Keep [.t2, .t3, .t4] s u := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hu : 8 * w + 8 * w * k ≤ r.length := h.mr.used
  rw [hrl] at hu
  have r144 : s.mem.readW (B + 144#64) 64 = BitVec.ofNat 64 rl := ctx.randLen
  have r152 : s.mem.readW (B + 152#64) 64 = BitVec.ofNat 64 (8 * w + 8 * w * k) := h.used
  have r216 : s.mem.readW (B + 216#64) 64 = BitVec.ofNat 64 (8 * w) := ctx.k
  have hrl64 := ctx.rl64
  have esub : BitVec.ofNat 64 rl - BitVec.ofNat 64 (8 * w + 8 * w * k) =
      BitVec.ofNat 64 (rl - (8 * w + 8 * w * k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have hD : 8 * w < 2 ^ 64 := by have := e.hw'; omega_arith
  refine WP.mono (WP.rdwr (WP.keep _ (Q := fun u =>
      u.gpr .t4 = BitVec.ofNat 64 (if rl - (8 * w + 8 * w * k) < 8 * w then 1 else 0) ∧ u.mem = s.mem) ?_
    (by rfl) (by rfl))) fun u ⟨⟨⟨u4, um⟩, ku⟩, rd, wr, sp⟩ => ⟨⟨⟨u4, um, sp⟩, rd, wr⟩, ku⟩
  simp only [tapeShort, ldh, hRandLen, hUsed, hK]
  brun [e.s6, e.hs.ld (d := 144) (n := 8) (by omega_arith), e.hs.al8 (d := 144) (by omega_arith) (by decide),
    e.hs.ld (d := 152) (n := 8) (by omega_arith), e.hs.al8 (d := 152) (by omega_arith) (by decide),
    e.hs.ld (d := 216) (n := 8) (by omega_arith), e.hs.al8 (d := 216) (by omega_arith) (by decide),
    r144, r152, r216, esub,
    VG.Proof.MillerRabin.RISCV64.Blinded.lt_flag (show rl - (8 * w + 8 * w * k) < 2 ^ 64 by omega_arith) hD]

/-- One iteration of the loop, from `k` witnesses with `n + 1` iterations
left: it ends with `MOut`, or goes on from `k + 1` with fewer left. -/
theorem body_ok (Ri : RoundImpl) {σ s : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand} {k n : Nat}
    (h : LInv σ s B R L w c rl ch r k n)
    (hpt : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) =
      loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w))) :
    WP isa (.seq (.block tapeShort)
        (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat])
            (VG.Impl.RsaKeyGen.RISCV64.Witness.draw Ri.name Ri.code))
          (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) s fun s' =>
      (isa.eval (.zero .t2) s' = some false ∧ n = 0 ∧ MOut σ s' B L w c rl r) ∨
      (isa.eval (.zero .t2) s' = some true ∧ 0 < n ∧ LInv σ s' B R L w c rl ch r (k + 1) (n - 1)) := by
  have ctx := h.ctx
  have e := ctx.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hwb := ctx.wb
  have hrl : r.length = rl := by rw [← h.tape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  have hu : 8 * w + 8 * w * k ≤ r.length := h.mr.used
  rw [hrl] at hu
  -- How many octets are left.
  refine WP.seq (WP.mono (check_ok h) fun u ⟨⟨⟨u4, um, usp⟩, urd, uwr⟩, ku⟩ => ?_)
  have hu' : LInv σ u B R L w c rl ch r k n := h.ofMem um ku usp
  have eu : Env u B (8 * L) w := hu'.ctx.prep.env
  refine WP.seq (WP.ite _ (Steps.eval_nonzero u .t4) (fun hz => ?_) (fun hz => ?_))
  · -- Too few octets left.
    have hn : ¬ 8 * w ≤ rl - (8 * w + 8 * w * k) := fun hp => by
      rw [u4] at hz; simp only [Nat.not_lt.mpr hp, ↓reduceIte] at hz; exact absurd hz (by decide)
    obtain ⟨hn0, hl⟩ := VG.Proof.RsaKeyGen.mrLoopAt_short h.mr hwb (by omega_arith) (by rw [hrl]; omega_arith)
    refine WP.mono (WP.rdwr (VG.Proof.MillerRabin.RISCV64.Blinded.setStat_ok (v := 0) eu (by decide)))
      fun x ⟨⟨⟨xm, xsp⟩, kx⟩, _, _, _⟩ => ?_
    have fx : Frm B (kgR w) u.mem x.mem := by
      rw [xm]
      refine VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen (rs := [(8 * hStat, 8)])
        (Frm.of_outside (o := 8 * hStat) (n := 8) (writeW_outside _ _ _ (by simp only [hStat]; omega_arith)) (by simp))
        ?_
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨(8 * hUsed, 16), by simp [kgR], by simp only [hUsed, hStat]; omega_arith,
        by simp only [hUsed, hStat]; omega_arith⟩
    have lx := hu'.keep.ofKgR kx fx xsp
    refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 0) lx.prep.env
        (by rw [xm]; exact word_writeW_self _ _ _ _) (by decide))
      fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => ?_
    refine .inl ⟨by rw [yev]; rfl, hn0, lx.ofKgR ky (by rw [ym]; exact Frm.refl _ _ _) ysp, ?_⟩
    show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
      | none => word y.mem B (8 * hStat) = BitVec.ofNat 64 0
      | some (b, rest) => word y.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
          word y.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
    rw [hpt, hl, ym, xm]
    exact word_writeW_self _ _ _ _
  · -- A draw.
    have hp : 8 * w ≤ rl - (8 * w + 8 * w * k) := by
      by_contra hp
      rw [u4] at hz; simp only [Nat.lt_of_not_le hp, ↓reduceIte] at hz; exact absurd hz (by decide)
    refine WP.mono (draw_ok Ri hu' (by omega_arith)) fun x ⟨lk, ux, hcase⟩ => ?_
    have hdrop : rl - (r.drop (8 * w + 8 * w * (k + 1))).length = 8 * w + 8 * w * (k + 1) := by
      rw [List.length_drop, hrl]
      have : 8 * w * (k + 1) = 8 * w * k + 8 * w := Nat.mul_succ _ _
      omega_arith
    rcases hcase with ⟨hn0, st2, hl⟩ | ⟨hn0, st1, hl⟩ | ⟨hn, li⟩
    · refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 2) lk.prep.env st2 (by decide))
        fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => ?_
      refine .inl ⟨by rw [yev]; rfl, hn0, lk.ofKgR ky (by rw [ym]; exact Frm.refl _ _ _) ysp, ?_⟩
      show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
        | none => word y.mem B (8 * hStat) = BitVec.ofNat 64 0
        | some (b, rest) => word y.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
            word y.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
      rw [hpt, hl, ym]
      exact ⟨st2, by rw [hdrop]; exact ux⟩
    · refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 1) lk.prep.env st1 (by decide))
        fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => ?_
      refine .inl ⟨by rw [yev]; rfl, hn0, lk.ofKgR ky (by rw [ym]; exact Frm.refl _ _ _) ysp, ?_⟩
      show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
        | none => word y.mem B (8 * hStat) = BitVec.ofNat 64 0
        | some (b, rest) => word y.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
            word y.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
      rw [hpt, hl, ym]
      exact ⟨st1, by rw [hdrop]; exact ux⟩
    · refine WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.tail_ok (v := 4) li.ctx.prep.env li.stat (by decide))
        fun y ⟨⟨⟨yev, ym, ysp⟩, yrd, ywr⟩, ky⟩ => .inr ⟨by rw [yev]; rfl, hn, li.ofMem ym ky ysp⟩

/-- The loop's first iteration count: one less than the iterations of the
specification's loop from the octets after the candidate. -/
def iters0 (c ch w : Nat) (r : Rand) : Nat :=
  VG.Proof.RsaKeyGen.itersOf (8 * w) r.length
    (VG.Proof.RsaKeyGen.shapeOf (loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2)
      (1, 0) (r.drop (8 * w)))) (8 * w) - 1

/-- The loop's counts, `hIdx := 1`, `hUni := 0` and `hStat := 4`: the
invariant from no witnesses. -/
theorem init_ok {σ : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand}
    (h : KCtx σ B L w c R rl ch) (hu : word σ.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w))
    (htape : Spec.Rsa.bytesAt σ.mem R rl = r) (h8 : 8 * w ≤ rl) :
    WP isa (.block [.li .t2 1, sth .t2 hIdx, .li .t2 0, sth .t2 hUni, .li .t2 4, sth .t2 hStat]) σ fun s0 =>
      LInv σ s0 B R L w c rl ch r 0 (iters0 c ch w r) := by
  have e := h.prep.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have hw4 := e.hw
  have hwb := h.wb
  have hrl : r.length = rl := by rw [← htape]; exact VG.Proof.RsaKeyGen.rand_bytes_length _ _ _
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun s0 => s0.mem = ((σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)).writeW
      (off B (8 * hUni)) (BitVec.ofNat 64 0)).writeW (off B (8 * hStat)) (BitVec.ofNat 64 4))
    (by simp only [sth, hIdx, hUni, hStat]
        brun [exec_li (show imm12 1 by decide), exec_li (show imm12 0 by decide), exec_li (show imm12 4 by decide),
          e.s6, e.hs.st (d := 176) (n := 8) (by omega_arith), e.hs.al8 (d := 176) (by omega_arith) (by decide),
          e.hs.st (d := 16) (n := 8) (by omega_arith), e.hs.al8 (d := 16) (by omega_arith) (by decide),
          e.hs.st (d := 160) (n := 8) (by omega_arith), e.hs.al8 (d := 160) (by omega_arith) (by decide)])
      (by rfl) (by rfl))) fun s0 ⟨⟨m0, k0⟩, rd0, wr0, sp0⟩ => ?_
  have o1 := writeW_outside σ.mem B (BitVec.ofNat 64 1) (d := 8 * hIdx) (by simp only [hIdx]; omega_arith)
  have o2 := writeW_outside (σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)) B (BitVec.ofNat 64 0)
    (d := 8 * hUni) (by simp only [hUni]; omega_arith)
  have o3 := writeW_outside ((σ.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)).writeW (off B (8 * hUni))
    (BitVec.ofNat 64 0)) B (BitVec.ofNat 64 4) (d := 8 * hStat) (by simp only [hStat]; omega_arith)
  have f0 : Frm B (kgR w) σ.mem s0.mem := by
    rw [m0]
    refine Frm.trans (Frm.trans (Frm.of_outside o1 (by simp [kgR])) (Frm.of_outside o2 (by simp [kgR])))
      (VG.Proof.MillerRabin.RISCV64.Blinded.frm_widen (rs := [(8 * hStat, 8)]) (Frm.of_outside o3 (by simp)) ?_)
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨(8 * hUsed, 16), by simp [kgR], by simp only [hUsed, hStat]; omega_arith,
      by simp only [hUsed, hStat]; omega_arith⟩
  have e0 : Env s0 B (8 * L) w := e.keep k0 (by decide)
  have ctx0 := h.ofKgR e0 (k0.gpr (by decide)) f0 rd0 wr0 sp0
  have fr0 : Frame [⟨B, 8 * L⟩, below σ.sp 96] σ.mem s0.mem := frame_of_kgR f0 hZ _
  have hd := fun d (h1 : d + 8 ≤ 8 * hIdx ∨ 8 * hIdx + 8 ≤ d) (h2 : d + 8 ≤ 8 * hUni ∨ 8 * hUni + 8 ≤ d)
      (h3 : d + 8 ≤ 8 * hStat ∨ 8 * hStat + 8 ≤ d) (h4 : d + 8 ≤ 2 ^ 64) =>
    (o3.word h3 h4).trans ((o2.word h2 h4).trans (o1.word h1 h4))
  refine ⟨ctx0, ?_, ?_, ?_, ?_, ?_, fr0, sp0, rd0, wr0, k0.gpr (by decide),
    VG.Proof.RsaKeyGen.mrLoopAt_zero hwb (by omega_arith) (by rw [hrl]; exact h8)⟩
  · rw [m0, hd _ (by simp only [hUsed, hIdx]; omega_arith) (by simp only [hUsed, hUni]; omega_arith)
      (by simp only [hUsed, hStat]; omega_arith) (by simp only [hUsed]; omega_arith), hu, Nat.mul_zero, Nat.add_zero]
  · rw [m0, o3.word (by simp only [hIdx, hStat]; omega_arith) (by simp only [hIdx]; omega_arith),
      o2.word (by simp only [hIdx, hUni]; omega_arith) (by simp only [hIdx]; omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [m0, o3.word (by simp only [hUni, hStat]; omega_arith) (by simp only [hUni]; omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [m0]; exact word_writeW_self _ _ _ _
  · rw [← htape]
    exact h.bytes_frame fr0

/-- RSA's witnesses, after the candidate's `8 w` octets: `MOut`. -/
theorem millerRabin_ok (Ri : RoundImpl) {σ : State} {B R : Addr} {L w c rl ch : Nat} {r : Rand}
    (h : KCtx σ B L w c R rl ch) (hu : word σ.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w))
    (htape : Spec.Rsa.bytesAt σ.mem R rl = r) (h8 : 8 * w ≤ rl)
    (hpt : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) =
      loop (mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (r.drop (8 * w))) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin Ri.name Ri.code) σ fun s' => MOut σ s' B L w c rl r := by
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin
  refine WP.seq (WP.mono (init_ok h hu htape h8) fun s0 l0 => ?_)
  refine WP.loop (Q := fun s' => MOut σ s' B L w c rl r)
    (fun n s => ∃ k, LInv σ s B R L w c rl ch r k n) (fun n s ⟨k, hk⟩ => ?_) _ s0 ⟨0, l0⟩
  exact WP.mono (body_ok Ri hk hpt) fun s' hs => hs.elim (fun ⟨ev, _, q⟩ => .inl ⟨ev, q⟩)
    (fun ⟨ev, hn, li⟩ => .inr ⟨ev, n - 1, by omega_arith, k + 1, li⟩)

end VG.Proof.RsaKeyGen.RISCV64.Cand
