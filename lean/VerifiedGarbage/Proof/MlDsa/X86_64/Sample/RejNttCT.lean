import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Common
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Ball
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt4

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge`. -/
section

/-!
# ML-DSA on x86-64: the sampling functions' SHAKE

What the sampling functions share (`Impl/MlDsa/X86_64/Sample/Common.lean`),
for any of them: a call is described by `Sp` (the message, its length, the
working space, the output polynomial and the parameter kept in `r12`), whose
regions are laid out as `SpOk` says. From the prologue on, `Env` holds: the
registers of the layout, the caller's callee-saved registers (in their
registers or saved in the working space), and the memory changed only in the
output, the working space and the stack below `rsp`. `sponge` then leaves
`outlen` bytes of SHAKE of the message at `scratch + 840` (`sponge_ok`),
leaking only the pointers and the length (`sponge_ct`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Spec.Sha3 (bytesAt stateAt rates)
open VG.Proof.MlDsa.Sample (padded)

/-- A call of a sampling function. -/
structure Sp where
  /-- The message hashed. -/
  sd : Addr
  len : Nat
  /-- `scratch`. -/
  scr : Addr
  /-- The output polynomial. -/
  a : Addr
  /-- The parameter, in `r12`. -/
  prm : BitVec 64

namespace Sp
variable (P : VG.Proof.MlDsa.X86_64.Sample.Sp)
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := P.scr + BitVec.ofNat 64 off
abbrev scrR : Region := ⟨P.scr, 2048⟩
abbrev sdR : Region := ⟨P.sd, P.len⟩
end Sp

/-- The regions of a call from the entry state `σ`. -/
structure SpOk (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ : State) : Prop where
  rd : σ.rd = [P.sdR]
  wr : σ.wr = [pR P.a, P.scrR]
  sd_a : P.sdR.Disjoint (pR P.a)
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : (pR P.a).Disjoint P.scrR
  ret_sd : (retR σ).Disjoint P.sdR
  ret_a : (retR σ).Disjoint (pR P.a)
  ret_scr : (retR σ).Disjoint P.scrR
  stk_sd : (below (σ.gpr .rsp) 16).Disjoint P.sdR
  stk_a : (below (σ.gpr .rsp) 16).Disjoint (pR P.a)
  stk_scr : (below (σ.gpr .rsp) 16).Disjoint P.scrR
  scr_end : P.scr.toNat + 2048 ≤ 2 ^ 64
  len_lt : P.len < 2 ^ 64

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = P.scr
  rbp : s.gpr .rbp = P.a
  r12 : s.gpr .r12 = P.prm
  rsp : s.gpr .rsp = σ.gpr .rsp
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], s.gpr r = σ.gpr r
  saved : s.mem.readW (P.at' 2024) 64 = σ.gpr .rbx ∧ s.mem.readW (P.at' 2032) 64 = σ.gpr .rbp ∧
    s.mem.readW (P.at' 2040) 64 = σ.gpr .r12
  frame : Frame [pR P.a, P.scrR, below (σ.gpr .rsp) 16] σ.mem s.mem

theorem r13_not {r : Reg} (hr : r ∈ [Reg.r13, .r14, .r15]) :
    r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

section
variable {P : VG.Proof.MlDsa.X86_64.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.X86_64.Sample.SpOk P σ)
include hp

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨P.at' a, n⟩ P.scrR := Offset.sub_base _ h

omit hp in
theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨P.scr, n⟩ P.scrR := Region.sub_prefix h

omit hp in
theorem disj_scr {a n b m : Nat} (h : a + n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨P.at' a, n⟩ ⟨P.at' b, m⟩ := Offset.disjoint _ (.inl h) (by omega) (by omega)

omit hp in
theorem disj_scr0 {n b m : Nat} (h : n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨P.scr, n⟩ ⟨P.at' b, m⟩ := Offset.base_disjoint _ h (by omega)

theorem sd_scr' {a n : Nat} (h : a + n ≤ 2048) : P.sdR.Disjoint ⟨P.at' a, n⟩ := hp.sd_scr.sub_right (VG.Proof.MlDsa.X86_64.Sample.sub_scr h)

theorem stk_scr' {a n : Nat} (h : a + n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨P.at' a, n⟩ :=
  hp.stk_scr.sub_right (VG.Proof.MlDsa.X86_64.Sample.sub_scr h)

theorem a_scr' {a n : Nat} (h : a + n ≤ 2048) : (pR P.a).Disjoint ⟨P.at' a, n⟩ :=
  hp.a_scr.sub_right (VG.Proof.MlDsa.X86_64.Sample.sub_scr h)

theorem sd_scr0 {n : Nat} (h : n ≤ 2048) : P.sdR.Disjoint ⟨P.scr, n⟩ := hp.sd_scr.sub_right (VG.Proof.MlDsa.X86_64.Sample.sub_scr0 h)

theorem stk_scr0 {n : Nat} (h : n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨P.scr, n⟩ :=
  hp.stk_scr.sub_right (VG.Proof.MlDsa.X86_64.Sample.sub_scr0 h)

omit hp in
theorem contains_scr {a n : Nat} (h : a + n ≤ 2048) : P.scrR.Contains (P.at' a) n :=
  Offset.contains_base _ h (by omega)

/-- The message is not written. -/
theorem sd_frame {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) : bytesAt s.mem P.sd P.len = bytesAt σ.mem P.sd P.len :=
  MlKem.bytesAt_frame he.frame (by simpa using ⟨hp.sd_a, hp.sd_scr, hp.stk_sd.symm⟩) (by have := hp.len_lt; omega)

/-- A word of the working space from byte 2024 on (a saved register) is apart
from the first 2024 bytes, the output polynomial and the stack. -/
theorem saved_apart {k : Nat} (hk : 2024 ≤ k) (hk' : k + 8 ≤ 2048) {sp : Addr} (hsp : sp = σ.gpr .rsp) :
    ∀ r ∈ [(⟨P.scr, 2024⟩ : Region), pR P.a, below sp 16], (⟨P.at' k, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (VG.Proof.MlDsa.X86_64.Sample.disj_scr0 (n := 2024) hk hk').symm
  · exact (VG.Proof.MlDsa.X86_64.Sample.a_scr' hp hk').symm
  · subst hsp; exact (VG.Proof.MlDsa.X86_64.Sample.stk_scr' hp hk').symm

/-- A call that writes within the first 2024 bytes of the working space and
the stack keeps `Env`. -/
theorem Env.call {s s' : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨P.scr, 2024⟩)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (rs ++ [below (s.gpr .rsp) 16]) s.mem s'.mem) : VG.Proof.MlDsa.X86_64.Sample.Env P σ s' := by
  have hsp : s'.gpr .rsp = s.gpr .rsp := hcs .rsp (by simp [calleeSaved])
  have hd : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ rs ++ [below (s.gpr .rsp) 16],
      (⟨P.at' k, 8⟩ : Region).Disjoint r := by
    intro k hk hk' r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (VG.Proof.MlDsa.X86_64.Sample.saved_apart hp hk hk' rfl _ (by simp)).sub_right (hrs r hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.MlDsa.X86_64.Sample.saved_apart hp hk hk' he.rsp _ (by simp)
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hcs .rbx (by simp [calleeSaved]), he.rbx],
    by rw [hcs .rbp (by simp [calleeSaved]), he.rbp], by rw [hcs .r12 (by simp [calleeSaved]), he.r12],
    by rw [hsp, he.rsp], fun r hr => ?_, ?_, ?_⟩
  · have hr' : r ∈ calleeSaved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [hcs r hr', he.cs r hr]
  · rw [hf.readW (Region.contains_self _ _) (hd 2024 (by omega) (by omega)) (by decide),
      hf.readW (Region.contains_self _ _) (hd 2032 (by omega) (by omega)) (by decide),
      hf.readW (Region.contains_self _ _) (hd 2040 (by omega) (by omega)) (by decide)]
    exact he.saved
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨P.scrR, by simp, fun x h => VG.Proof.MlDsa.X86_64.Sample.sub_scr0 (P := P) (n := 2024) (by omega) x (hrs r hr x h)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (σ.gpr .rsp) 16, by simp, by rw [he.rsp]; exact fun _ h => h⟩

omit hp in
/-- `Env` after a block that writes only caller-saved registers and no memory. -/
theorem Env.keep {s s' : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) (hm : s'.mem = s.mem)
    (hk : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s') : VG.Proof.MlDsa.X86_64.Sample.Env P σ s' :=
  ⟨hk.2.1.trans he.rd, hk.2.2.trans he.wr, by rw [hk.gpr (by decide), he.rbx], by rw [hk.gpr (by decide), he.rbp],
    by rw [hk.gpr (by decide), he.r12], by rw [hk.gpr (by decide), he.rsp],
    fun r hr => by rw [hk.gpr (VG.Proof.MlDsa.X86_64.Sample.r13_not hr), he.cs r hr], by rw [hm]; exact he.saved, by rw [hm]; exact he.frame⟩

/-- The regions, from the prologue on. -/
theorem regions {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) : s.rd ++ s.wr = [P.sdR, pR P.a, P.scrR] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov_all {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, r = P.sdR ∨ ∃ off, r.base = P.scr + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) :
    Covers rs (s.rd ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rw [VG.Proof.MlDsa.X86_64.Sample.regions hp he]
    rcases h r hr with rfl | ⟨off, hb, hl⟩
    · exact ⟨P.sdR, by simp, 0, (add_ofNat_zero _).symm, by simp⟩
    · exact ⟨P.scrR, by simp, off, hb, hl⟩

theorem cov_scr {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.scr + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨P.scrR, by rw [he.wr, hp.wr]; simp, off, hb, hl⟩

theorem inScr {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) {a n : Nat} (h : a + n ≤ 2048) : InRegions s.wr (P.at' a) n := by
  rw [he.wr, hp.wr]
  exact ⟨P.scrR, by simp, VG.Proof.MlDsa.X86_64.Sample.contains_scr h⟩

theorem inScrRd {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (P.at' a) n := by
  rw [VG.Proof.MlDsa.X86_64.Sample.regions hp he]
  exact ⟨P.scrR, by simp, VG.Proof.MlDsa.X86_64.Sample.contains_scr h⟩

end

/-! ## The sponge -/

/-- The entry of `sponge`: the message in `rcx` and its length in `r8`. -/
structure J0 (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env P σ s
  rcx : s.gpr .rcx = P.sd
  r8 : s.gpr .r8 = BitVec.ofNat 64 P.len

/-- The message. -/
abbrev Sp.msg (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ : State) : List Byte := bytesAt σ.mem P.sd P.len

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env P σ s
  zero : stateAt s.mem P.scr = Spec.Sha3.zero
  args : AbsorbArgs s P.scr P.sd (P.at' 200) rate 0 P.len

theorem sx200 : BitVec.signExtend 64 (200 : BitVec 32) = BitVec.ofNat 64 200 := by decide
theorem sx840 : BitVec.signExtend 64 (840 : BitVec 32) = BitVec.ofNat 64 840 := by decide

theorem sw64 (x : BitVec 32) : BitVec.setWidth 64 x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The rates of SHAKE256 and SHAKE128. -/
def spRate (rate : BitVec 32) : Prop := rate.toNat = 136 ∨ rate.toNat = 168

theorem spRate_mem {rate : BitVec 32} (h : VG.Proof.MlDsa.X86_64.Sample.spRate rate) : rate.toNat ∈ rates := by
  rcases h with h | h <;> rw [h] <;> decide

theorem spRate_pos {rate : BitVec 32} (h : VG.Proof.MlDsa.X86_64.Sample.spRate rate) : 0 < rate.toNat := by rcases h with h | h <;> omega

section
variable {P : VG.Proof.MlDsa.X86_64.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.X86_64.Sample.SpOk P σ)
include hp

theorem blk1_ok {rate : BitVec 32} (hr : VG.Proof.MlDsa.X86_64.Sample.spRate rate) {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J0 P σ s) :
    WP isa (.block (zeroSt ++ absArgs rate)) s (VG.Proof.MlDsa.X86_64.Sample.J1 rate.toNat P σ) := by
  unfold zeroSt
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm1, hax⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  have hb1 : s1.gpr .rbx = P.scr := by rw [k1.gpr (by decide), h.env.rbx]
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => by
      rw [hb1, add_ofNat_zero, k1.2.2]; exact VG.Proof.MlDsa.X86_64.Sample.inScr hp h.env (by omega)) fun s2 ⟨hz, hf2, k2⟩ => ?_
  rw [hb1, add_ofNat_zero] at hz hf2
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .r9] (Q := fun s' => s'.mem = s2.mem ∧
      s'.gpr .rdi = P.scr ∧ s'.gpr .rsi = BitVec.ofNat 64 rate.toNat ∧ s'.gpr .rdx = BitVec.ofNat 64 0 ∧
      s'.gpr .r9 = P.at' 200)
    (by unfold absArgs; xrun [k2.gpr (r := .rbx) (by decide), hb1, VG.Proof.MlDsa.X86_64.Sample.sx200, VG.Proof.MlDsa.X86_64.Sample.sw64]) (by rfl))
    fun s3 ⟨⟨hm3, hdi, hsi, hdx, h9⟩, k3⟩ => ?_
  have e1 := h.env.keep hm1 (k1.mono (by decide))
  have k23 := (k2.trans k3)
  have hsp : s3.gpr .rsp = σ.gpr .rsp := by rw [k23.gpr (by decide), k1.gpr (by decide), h.env.rsp]
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 → s3.mem.readW (P.at' k) 64 = s1.mem.readW (P.at' k) 64 := by
    intro k hk hk'
    rw [hm3, hf2.readW (Region.contains_self _ _) (by
      simpa using (VG.Proof.MlDsa.X86_64.Sample.disj_scr0 (n := 200) (b := k) (m := 8) (by omega) hk').symm) (by decide)]
  refine ⟨⟨k23.2.1.trans e1.rd, k23.2.2.trans e1.wr, by rw [k23.gpr (by decide), e1.rbx],
    by rw [k23.gpr (by decide), e1.rbp], by rw [k23.gpr (by decide), e1.r12], hsp,
    fun r hr => by rw [k23.gpr (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide), e1.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact e1.saved), ?_⟩, by rw [hm3]; exact hz, ?_⟩
  · rw [hm3]
    exact e1.frame.trans (hf2.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨P.scrR, by simp, VG.Proof.MlDsa.X86_64.Sample.sub_scr0 (by omega)⟩)
  · have hcx : s3.gpr .rcx = P.sd := by rw [k23.gpr (by decide), k1.gpr (by decide), h.rcx]
    have h8 : s3.gpr .r8 = BitVec.ofNat 64 P.len := by rw [k23.gpr (by decide), k1.gpr (by decide), h.r8]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, VG.Proof.MlDsa.X86_64.Sample.spRate_mem hr, VG.Proof.MlDsa.X86_64.Sample.spRate_pos hr, hp.len_lt,
      VG.Proof.MlDsa.X86_64.Sample.disj_scr0 (by omega) (by omega), (VG.Proof.MlDsa.X86_64.Sample.sd_scr0 hp (by omega)), VG.Proof.MlDsa.X86_64.Sample.sd_scr' hp (by omega),
      by rw [hsp]; exact VG.Proof.MlDsa.X86_64.Sample.stk_scr0 hp (by omega), by rw [hsp]; exact hp.stk_sd,
      by rw [hsp]; exact VG.Proof.MlDsa.X86_64.Sample.stk_scr' hp (by omega)⟩

/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env P σ s
  repr : Spec.Sha3.Repr s.mem P.scr rate (P.msg σ)
  rax : s.gpr .rax = BitVec.ofNat 64 (P.len % rate)

theorem covA {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) :
    Covers ([P.sdR] ++ [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] s.wr := by
  refine ⟨VG.Proof.MlDsa.X86_64.Sample.cov_all hp he ?_, VG.Proof.MlDsa.X86_64.Sample.cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inl rfl, .inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]

omit hp in
theorem subA : ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' 200, 640⟩], Region.Sub r ⟨P.scr, 2024⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [Region.sub_prefix (by omega), Offset.sub_base _ (by omega)]

omit hp in
/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem call1_ok {rate : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J1 rate P σ s) :
    WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) s (VG.Proof.MlDsa.X86_64.Sample.J2 rate P σ) := by
  refine absorb_call h.args (VG.Proof.MlDsa.X86_64.Sample.covA hp h.env).1 (VG.Proof.MlDsa.X86_64.Sample.covA hp h.env).2 fun s' hrd hwr hcs hf hr hax =>
    ⟨Env.call hp h.env VG.Proof.MlDsa.X86_64.Sample.subA hrd hwr hcs hf, ?_, ?_⟩
  · have := hr [] (VG.Proof.MlDsa.X86_64.Sample.repr_nil h.zero) rfl
    rwa [List.nil_append, VG.Proof.MlDsa.X86_64.Sample.sd_frame hp h.env] at this
  · apply BitVec.eq_of_toNat_eq
    rw [hax, BitVec.toNat_ofNat, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ h.args.hpos) (rate_lt h.args.hrate))).symm

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env P σ s
  repr : Spec.Sha3.Repr s.mem P.scr rate (P.msg σ)
  args : PadArgs s P.scr (P.at' 200) rate (P.len % rate)
  rcx : (s.gpr .rcx).setWidth 8 = Spec.Sha3.shakeSuffix

theorem blk2_ok {rate : BitVec 32} (hr : VG.Proof.MlDsa.X86_64.Sample.spRate rate) {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J2 rate.toNat P σ s) :
    WP isa (.block (padArgs rate)) s (VG.Proof.MlDsa.X86_64.Sample.J3 rate.toNat P σ) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = P.scr ∧ s'.gpr .rsi = BitVec.ofNat 64 rate.toNat ∧
      s'.gpr .rdx = BitVec.ofNat 64 (P.len % rate.toNat) ∧
      s'.gpr .rcx = BitVec.setWidth 64 (0x1f : BitVec 32) ∧ s'.gpr .r8 = P.at' 200)
    (by unfold padArgs; xrun [h.env.rbx, h.rax, VG.Proof.MlDsa.X86_64.Sample.sx200, VG.Proof.MlDsa.X86_64.Sample.sw64]) (by rfl))
    fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  exact ⟨he, by rw [hm]; exact h.repr, ⟨hdi, hsi, hdx, h8, VG.Proof.MlDsa.X86_64.Sample.spRate_mem hr, Nat.mod_lt _ (VG.Proof.MlDsa.X86_64.Sample.spRate_pos hr),
    VG.Proof.MlDsa.X86_64.Sample.disj_scr0 (by omega) (by omega), by rw [he.rsp]; exact VG.Proof.MlDsa.X86_64.Sample.stk_scr0 hp (by omega),
    by rw [he.rsp]; exact VG.Proof.MlDsa.X86_64.Sample.stk_scr' hp (by omega)⟩, by rw [hcx]; decide⟩

/-- After padding. -/
structure J4 (rate : Nat) (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env P σ s
  st : stateAt s.mem P.scr = VG.Proof.MlDsa.Sample.padded rate Spec.Sha3.shakeSuffix (P.msg σ)

theorem covP {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] s.wr :=
  ⟨fun a n h => (VG.Proof.MlDsa.X86_64.Sample.covA hp he).1 a n (by simp only [List.nil_append] at h; exact
                                 ⟨_, List.mem_append_right _ h.choose_spec.1, h.choose_spec.2⟩), (VG.Proof.MlDsa.X86_64.Sample.covA hp he).2⟩

theorem call2_ok {rate : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J3 rate P σ s) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) s (VG.Proof.MlDsa.X86_64.Sample.J4 rate P σ) := by
  obtain ⟨he, hrep, hargs, hcx⟩ := h
  refine pad_call hargs (VG.Proof.MlDsa.X86_64.Sample.covP hp he).1 (VG.Proof.MlDsa.X86_64.Sample.covP hp he).2 fun s' hrd hwr hcs hf hst =>
    ⟨Env.call hp he VG.Proof.MlDsa.X86_64.Sample.subA hrd hwr hcs hf, ?_⟩
  rw [hst (P.msg σ) hrep (by rw [MlKem.bytesAt_length]), hcx]

omit hp in
/-- The arguments of `squeeze`. -/
def J5 (rate outlen : Nat) (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sample.J4 rate P σ s ∧ SqueezeArgs s P.scr (P.at' 840) (P.at' 200) rate 0 outlen

theorem blk3_ok {rate outlen : BitVec 32} (hr : VG.Proof.MlDsa.X86_64.Sample.spRate rate) (ho : 840 + outlen.toNat ≤ 2024) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sample.J4 rate.toNat P σ s) : WP isa (.block (sqzArgs rate outlen)) s (VG.Proof.MlDsa.X86_64.Sample.J5 rate.toNat outlen.toNat P σ) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = P.scr ∧ s'.gpr .rsi = BitVec.ofNat 64 rate.toNat ∧ s'.gpr .rdx = BitVec.ofNat 64 0 ∧
      s'.gpr .rcx = P.at' 840 ∧ s'.gpr .r8 = BitVec.ofNat 64 outlen.toNat ∧ s'.gpr .r9 = P.at' 200)
    (by unfold sqzArgs; xrun [h.env.rbx, VG.Proof.MlDsa.X86_64.Sample.sx200, VG.Proof.MlDsa.X86_64.Sample.sx840, VG.Proof.MlDsa.X86_64.Sample.sw64]) (by rfl))
    fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  refine ⟨⟨he, by rw [hm]; exact h.st⟩, ⟨hdi, hsi, hdx, hcx, h8, h9, VG.Proof.MlDsa.X86_64.Sample.spRate_mem hr, Nat.zero_le _, by omega,
    VG.Proof.MlDsa.X86_64.Sample.disj_scr0 (by omega) (by omega), VG.Proof.MlDsa.X86_64.Sample.disj_scr0 (by omega) (by omega),
    (VG.Proof.MlDsa.X86_64.Sample.disj_scr (a := 200) (n := 640) (b := 840) (m := outlen.toNat) (by omega) (by omega)).symm,
    by rw [he.rsp]; exact VG.Proof.MlDsa.X86_64.Sample.stk_scr0 hp (by omega), by rw [he.rsp]; exact VG.Proof.MlDsa.X86_64.Sample.stk_scr' hp (by omega),
    by rw [he.rsp]; exact VG.Proof.MlDsa.X86_64.Sample.stk_scr' hp (by omega)⟩⟩

/-- After squeezing: the output. -/
structure J6 (rate outlen : Nat) (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env P σ s
  out : bytesAt s.mem (P.at' 840) outlen = Spec.Sha3.squeezeFrom rate (VG.Proof.MlDsa.Sample.padded rate Spec.Sha3.shakeSuffix (P.msg σ)) 0 outlen

theorem covS {outlen : Nat} (ho : 840 + outlen ≤ 2024) {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) :
    Covers ([] ++ [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩] s.wr := by
  refine ⟨VG.Proof.MlDsa.X86_64.Sample.cov_all hp he ?_, VG.Proof.MlDsa.X86_64.Sample.cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨840, rfl, by simp; omega⟩,
      .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩, ⟨200, rfl, by simp⟩]

theorem call3_ok {rate outlen : Nat} (ho : 840 + outlen ≤ 2024) {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J5 rate outlen P σ s) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) s (VG.Proof.MlDsa.X86_64.Sample.J6 rate outlen P σ) := by
  obtain ⟨h, hargs⟩ := h
  have cov := VG.Proof.MlDsa.X86_64.Sample.covS hp ho h.env
  have sub : ∀ r ∈ [(⟨P.scr, 200⟩ : Region), ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩],
      Region.Sub r ⟨P.scr, 2024⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [Region.sub_prefix (by omega), Offset.sub_base _ (by omega), Offset.sub_base _ (by omega)]
  refine squeeze_call hargs cov.1 cov.2 fun s' hrd hwr hcs hf ho' => ⟨Env.call hp h.env sub hrd hwr hcs hf, ?_⟩
  rw [ho', h.st]

/-- The sponge, from `J0`. -/
theorem sponge_ok {rate outlen : BitVec 32} (hr : VG.Proof.MlDsa.X86_64.Sample.spRate rate) (ho : 840 + outlen.toNat ≤ 2024) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sample.J0 P σ s) : WP isa (sponge rate outlen) s (VG.Proof.MlDsa.X86_64.Sample.J6 rate.toNat outlen.toNat P σ) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.blk1_ok hp hr h) fun _ h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.call1_ok hp h1) fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.blk2_ok hp hr h2) fun _ h3 =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.call2_ok hp h3) fun _ h4 => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.blk3_ok hp hr ho h4) fun _ h5 =>
        VG.Proof.MlDsa.X86_64.Sample.call3_ok hp ho h5)))))

end

/-! ## Constant time -/

/-- Two calls whose public data agree. -/
structure SpPub (P₁ P₂ : VG.Proof.MlDsa.X86_64.Sample.Sp) (σ₁ σ₂ : State) : Prop where
  sd : P₁.sd = P₂.sd
  len : P₁.len = P₂.len
  scr : P₁.scr = P₂.scr
  a : P₁.a = P₂.a
  prm : P₁.prm = P₂.prm
  rsp : σ₁.gpr .rsp = σ₂.gpr .rsp

/-- The registers of the layout agree. -/
theorem env_pub {P₁ P₂ : VG.Proof.MlDsa.X86_64.Sample.Sp} {σ₁ σ₂ s₁ s₂ : State} (hq : VG.Proof.MlDsa.X86_64.Sample.SpPub P₁ P₂ σ₁ σ₂) (e₁ : VG.Proof.MlDsa.X86_64.Sample.Env P₁ σ₁ s₁)
    (e₂ : VG.Proof.MlDsa.X86_64.Sample.Env P₂ σ₂ s₂) : s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .r12 = s₂.gpr .r12 ∧
      s₁.gpr .rsp = s₂.gpr .rsp := by
  rw [e₁.rbx, e₂.rbx, e₁.rbp, e₂.rbp, e₁.r12, e₂.r12, e₁.rsp, e₂.rsp, hq.scr, hq.a, hq.prm, hq.rsp]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem at_pub {P₁ P₂ : VG.Proof.MlDsa.X86_64.Sample.Sp} {σ₁ σ₂ : State} (hq : VG.Proof.MlDsa.X86_64.Sample.SpPub P₁ P₂ σ₁ σ₂) (k : Nat) : P₁.at' k = P₂.at' k := by
  simp only [Sp.at', hq.scr]

section
/-! The runs of a sampling function whose entry states satisfy `Pre` and
agree by `Pub`, each making the call `f σ` of its entry state `σ`. -/
variable {Pre : State → Prop} {Pub : State → State → Prop} {f : State → VG.Proof.MlDsa.X86_64.Sample.Sp}
  (hok : ∀ σ, Pre σ → VG.Proof.MlDsa.X86_64.Sample.SpOk (f σ) σ)
  (hpub : ∀ σ₁ σ₂, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → VG.Proof.MlDsa.X86_64.Sample.SpPub (f σ₁) (f σ₂) σ₁ σ₂)
include hok hpub

omit hpub in
/-- A piece that leaks the same from runs related by `J`, and takes each run
from `J` to `J'`. -/
theorem relSp {J J' : VG.Proof.MlDsa.X86_64.Sample.Sp → State → State → Prop} {c : Prog isa}
    (hw : ∀ P σ s, VG.Proof.MlDsa.X86_64.Sample.SpOk P σ → J P σ s → WP isa c s (J' P σ))
    (ht : RelCT isa (Rel2 Pre Pub fun σ => J (f σ) σ) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub fun σ => J (f σ) σ) c (Rel2 Pre Pub fun σ => J' (f σ) σ) :=
  relInv (fun σ s hp h => hw _ σ s (hok σ hp) h) ht

omit hok in
/-- Code the taint analysis proves constant time from `rbx`, `rbp`, `r12`
and `rsp`, and the registers `rs`, which agree in runs related by `J`. -/
theorem taintSp {J : VG.Proof.MlDsa.X86_64.Sample.Sp → State → State → Prop} (hJ : ∀ σ s, J (f σ) σ s → VG.Proof.MlDsa.X86_64.Sample.Env (f σ) σ s) {c : Prog isa}
    (rs : List Reg) (hr : ∀ s₁ s₂, Rel2 Pre Pub (fun σ => J (f σ) σ) s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (X86_64.Taint.ofRegs (([.rbx, .rbp, .r12, .rsp] : List Reg) ++ rs)) c hc).isSome = true) :
    RelCT isa (Rel2 Pre Pub fun σ => J (f σ) σ) c fun _ _ => True :=
  taintRel _ (fun s₁ s₂ hs r hr' => by
    rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨σ₁, σ₂, p₁, p₂, hq, i₁, i₂⟩ := hs
      have := VG.Proof.MlDsa.X86_64.Sample.env_pub (hpub σ₁ σ₂ p₁ p₂ hq) (hJ _ _ i₁) (hJ _ _ i₂)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
    · exact hr s₁ s₂ hs r hr') h

theorem sponge_ct {rate outlen : BitVec 32} (hr : VG.Proof.MlDsa.X86_64.Sample.spRate rate) (ho : 840 + outlen.toNat ≤ 2024)
    {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp]) (.block (zeroSt ++ absArgs rate)) h1).isSome
      = true)
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp, .rax]) (.block (padArgs rate)) h2).isSome = true)
    (c3 : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .rsp]) (.block (sqzArgs rate outlen)) h3).isSome
      = true) :
    RelCT isa (Rel2 Pre Pub fun σ => VG.Proof.MlDsa.X86_64.Sample.J0 (f σ) σ) (sponge rate outlen)
      (Rel2 Pre Pub fun σ => VG.Proof.MlDsa.X86_64.Sample.J6 rate.toNat outlen.toNat (f σ) σ) := by
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sample.relSp hok (J' := VG.Proof.MlDsa.X86_64.Sample.J1 rate.toNat) (fun P σ s hp h => VG.Proof.MlDsa.X86_64.Sample.blk1_ok hp hr h)
    (VG.Proof.MlDsa.X86_64.Sample.taintSp hpub (fun _ _ h => h.env) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by simpa using c1))) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sample.relSp hok (J' := VG.Proof.MlDsa.X86_64.Sample.J2 rate.toNat) (fun P σ s hp h => VG.Proof.MlDsa.X86_64.Sample.call1_ok hp h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)) ?_
  · have hq := hpub σ₁ σ₂ p₁ p₂ hq'
    have o₁ := hok σ₁ p₁
    have o₂ := hok σ₂ p₂
    refine ⟨_, _, _, _, absorb_pre h₁.args, absorb_pre h₂.args, ?_, (VG.Proof.MlDsa.X86_64.Sample.covA o₁ h₁.env).1, (VG.Proof.MlDsa.X86_64.Sample.covA o₁ h₁.env).2,
      (VG.Proof.MlDsa.X86_64.Sample.covA o₂ h₂.env).1, (VG.Proof.MlDsa.X86_64.Sample.covA o₂ h₂.env).2, (VG.Proof.MlDsa.X86_64.Sample.env_pub hq h₁.env h₂.env).2.2.2⟩
    simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
      ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
      h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8,
      h₁.args.r9, h₂.args.r9, hq.scr, hq.sd, hq.len, VG.Proof.MlDsa.X86_64.Sample.at_pub hq, (VG.Proof.MlDsa.X86_64.Sample.env_pub hq h₁.env h₂.env).2.2.2, and_self]
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sample.relSp hok (J' := VG.Proof.MlDsa.X86_64.Sample.J3 rate.toNat) (fun P σ s hp h => VG.Proof.MlDsa.X86_64.Sample.blk2_ok hp hr h)
    (VG.Proof.MlDsa.X86_64.Sample.taintSp hpub (fun _ _ h => h.env) [.rax] (fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, i₁, i₂⟩ r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [i₁.rax, i₂.rax, (hpub σ₁ σ₂ p₁ p₂ hq).len]) (by simpa using c2))) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sample.relSp hok (J' := VG.Proof.MlDsa.X86_64.Sample.J4 rate.toNat) (fun P σ s hp h => VG.Proof.MlDsa.X86_64.Sample.call2_ok hp h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)) ?_
  · have hq := hpub σ₁ σ₂ p₁ p₂ hq'
    have o₁ := hok σ₁ p₁
    have o₂ := hok σ₂ p₂
    refine ⟨_, _, _, _, pad_pre h₁.args, pad_pre h₂.args, ?_, (VG.Proof.MlDsa.X86_64.Sample.covP o₁ h₁.env).1, (VG.Proof.MlDsa.X86_64.Sample.covP o₁ h₁.env).2,
      (VG.Proof.MlDsa.X86_64.Sample.covP o₂ h₂.env).1, (VG.Proof.MlDsa.X86_64.Sample.covP o₂ h₂.env).2, (VG.Proof.MlDsa.X86_64.Sample.env_pub hq h₁.env h₂.env).2.2.2⟩
    simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.r8 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
      h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.r8, h₂.args.r8, hq.scr, hq.len, VG.Proof.MlDsa.X86_64.Sample.at_pub hq,
      (VG.Proof.MlDsa.X86_64.Sample.env_pub hq h₁.env h₂.env).2.2.2, and_self]
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sample.relSp hok (J' := VG.Proof.MlDsa.X86_64.Sample.J5 rate.toNat outlen.toNat) (fun P σ s hp h => VG.Proof.MlDsa.X86_64.Sample.blk3_ok hp hr ho h)
    (VG.Proof.MlDsa.X86_64.Sample.taintSp hpub (fun _ _ h => h.env) [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by simpa using c3))) ?_
  refine VG.Proof.MlDsa.X86_64.Sample.relSp hok (fun P σ s hp h => VG.Proof.MlDsa.X86_64.Sample.call3_ok hp ho h)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
      fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq', h₁, h₂⟩ => ?_)
  have hq := hpub σ₁ σ₂ p₁ p₂ hq'
  have o₁ := hok σ₁ p₁
  have o₂ := hok σ₂ p₂
  refine ⟨_, _, _, _, squeeze_pre h₁.2, squeeze_pre h₂.2, ?_, (VG.Proof.MlDsa.X86_64.Sample.covS o₁ ho h₁.1.env).1, (VG.Proof.MlDsa.X86_64.Sample.covS o₁ ho h₁.1.env).2,
    (VG.Proof.MlDsa.X86_64.Sample.covS o₂ ho h₂.1.env).1, (VG.Proof.MlDsa.X86_64.Sample.covS o₂ ho h₂.1.env).2, (VG.Proof.MlDsa.X86_64.Sample.env_pub hq h₁.1.env h₂.1.env).2.2.2⟩
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
      ce_gpr _ (by decide : Reg.rdi ≠ .rsp), ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr _ (by decide : Reg.rdx ≠ .rsp), ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
      ce_gpr _ (by decide : Reg.r8 ≠ .rsp), ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.2.rdi, h₂.2.rdi,
      h₁.2.rsi, h₂.2.rsi, h₁.2.rdx, h₂.2.rdx, h₁.2.rcx, h₂.2.rcx, h₁.2.r8, h₂.2.r8,
      h₁.2.r9, h₂.2.r9, hq.scr, VG.Proof.MlDsa.X86_64.Sample.at_pub hq, (VG.Proof.MlDsa.X86_64.Sample.env_pub hq h₁.1.env h₂.1.env).2.2.2, and_self]

end

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro`. -/
section

/-!
# ML-DSA on x86-64: the sampling functions' prologue and epilogue

The prologue (`pro`) saves `rbx`, `rbp` and `r12` in the working space and
sets up the layout: from what running it leaves, `J0` holds (`pro_J0`). The
epilogue (`epi`) restores them: with `Env`, the calling convention's
obligations hold at the end (`epi_ok`). A coefficient store of a loop (`[rbp +
4 rdi]`) is apart from everything `Env` keeps (`ea_aJ`, `Env.store`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample (coeffAddr polyR coeff_contains)
open VG.Spec.Sha3 (bytesAt)

section
variable {P : VG.Proof.MlDsa.X86_64.Sample.Sp} {σ : State} (hp : VG.Proof.MlDsa.X86_64.Sample.SpOk P σ)
include hp

/-- A word of the working space, in the regions of the entry state. -/
theorem inScrσ {a n : Nat} (h : a + n ≤ 2048) : InRegions σ.wr (P.at' a) n := by
  rw [hp.wr]
  exact ⟨P.scrR, by simp, VG.Proof.MlDsa.X86_64.Sample.contains_scr h⟩

omit hp in
/-- What running the prologue leaves: `J0`. -/
theorem pro_J0 {s : State}
    (hm : s.mem = ((σ.mem.writeW (P.at' 2024) (σ.gpr .rbx)).writeW (P.at' 2032) (σ.gpr .rbp)).writeW
      (P.at' 2040) (σ.gpr .r12))
    (hbx : s.gpr .rbx = P.scr) (hbp : s.gpr .rbp = P.a) (h12 : s.gpr .r12 = P.prm) (hcx : s.gpr .rcx = P.sd)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 P.len) (hk : Keep [.rbx, .rbp, .r12, .rcx, .r8] σ s) : VG.Proof.MlDsa.X86_64.Sample.J0 P σ s := by
  have sep : ∀ a b, 2024 ≤ a → a + 8 ≤ b → b + 8 ≤ 2048 →
      Mem.Sep (P.at' a) (64 / 8) (P.at' b) (64 / 8) := fun a b h1 h2 h3 =>
    Offset.sep _ (.inl h2) (by omega) (by omega)
  have sep' : ∀ a b, 2024 ≤ b → b + 8 ≤ a → a + 8 ≤ 2048 →
      Mem.Sep (P.at' a) (64 / 8) (P.at' b) (64 / 8) := fun a b h1 h2 h3 =>
    Offset.sep _ (.inr h2) (by omega) (by omega)
  have hin : ∀ a, a + 8 ≤ 2048 → P.scrR.Contains (P.at' a) (64 / 8) := fun a ha => VG.Proof.MlDsa.X86_64.Sample.contains_scr ha
  refine ⟨⟨hk.2.1, hk.2.2, hbx, hbp, h12, hk.gpr (by decide), fun r hr => hk.gpr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide), ?_, ?_⟩, hcx, h8⟩
  · rw [hm, Mem.readW_writeW_sep (sep 2024 2040 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 2024 2032 (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 2032 2040 (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_self64]
    exact ⟨rfl, rfl, rfl⟩
  · rw [hm]
    exact (((Frame.refl _ _).writeW (by simp) _ (hin 2024 (by omega))).writeW (by simp) _
      (hin 2032 (by omega))).writeW (by simp) _ (hin 2040 (by omega))

/-- The epilogue: `rbx`, `rbp` and `r12` restored. -/
theorem epi_ok {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.epi) s fun s' => (s'.gpr .rbx = σ.gpr .rbx ∧ s'.gpr .rbp = σ.gpr .rbp ∧
      s'.gpr .r12 = σ.gpr .r12 ∧ s'.mem = s.mem) ∧ Keep [.rbp, .r12, .rbx] s s' := by
  refine WP.keep _ ?_ (by decide)
  have e := he.saved
  unfold VG.Impl.MlDsa.X86_64.Sample.epi
  xrun [he.rbx, VG.Proof.MlDsa.X86_64.Sample.inScrRd hp he (a := 2024) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Sample.inScrRd hp he (a := 2032) (n := 8) (by omega),
    VG.Proof.MlDsa.X86_64.Sample.inScrRd hp he (a := 2040) (n := 8) (by omega), e.1, e.2.1, e.2.2]

omit hp in
theorem ret_below (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 16) :=
  (Offset.base_disjoint_below sp (n := 16) (k := 8) (by omega))

/-- The calling convention's obligations, at the end of a sampling function:
the callee-saved registers restored and the return address not written. -/
theorem gpr_end {s s' : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) (hbx : s'.gpr .rbx = σ.gpr .rbx) (hbp : s'.gpr .rbp = σ.gpr .rbp)
    (h12 : s'.gpr .r12 = σ.gpr .r12) (hk : Keep [.rax, .rbp, .r12, .rbx] s s') (hm : s'.mem = s.mem) :
    gprPreserved σ s' := by
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hbx
    · exact hbp
    · rw [hk.gpr (by decide), he.rsp]
    · exact h12
    all_goals rw [hk.gpr (by decide)]; exact he.cs _ (by decide)
  · rw [hm]
    exact he.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, VG.Proof.MlDsa.X86_64.Sample.ret_below _⟩) (by decide)

omit hp in
theorem retJ_ok (s : State) :
    WP isa (.block retJ) s fun s' => (s'.gpr .rax = s.gpr .rdi >>> 8 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold retJ
  xrun

omit hp in
theorem ret_val {x : BitVec 64} {j : Nat} (hx : x = BitVec.ofNat 64 j) (hj : j ≤ 256) :
    (x >>> 8).setWidth 32 = if j = 256 then 1 else 0 := by
  subst hx
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, shr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)]
  split
  · subst j; rfl
  · rw [Nat.div_eq_of_lt (by omega)]; rfl

/-- The end of a sampling function that returns whether `j` (in `rdi`) is 256. -/
theorem retEpi_ok {s : State} (he : VG.Proof.MlDsa.X86_64.Sample.Env P σ s) {j : Nat} (hdi : s.gpr .rdi = BitVec.ofNat 64 j) (hj : j ≤ 256) :
    WP isa (.block (retJ ++ VG.Impl.MlDsa.X86_64.Sample.epi)) s fun s' =>
      (s'.gpr .rax).setWidth 32 = (if j = 256 then 1 else 0) ∧ s'.mem = s.mem ∧ gprPreserved σ s' := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.retJ_ok s) fun s1 ⟨⟨hax, hm1⟩, k1⟩ => ?_
  have he1 := he.keep hm1 (k1.mono (by decide))
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.epi_ok hp he1) fun s2 ⟨⟨hbx, hbp, h12, hm2⟩, k2⟩ =>
    ⟨by rw [k2.gpr (by decide), hax, VG.Proof.MlDsa.X86_64.Sample.ret_val hdi hj], by rw [hm2, hm1], ?_⟩
  exact VG.Proof.MlDsa.X86_64.Sample.gpr_end hp he hbx hbp h12 ((k1.trans k2).mono (rs' := [.rax, .rbp, .r12, .rbx]) (by simp)) (hm2.trans hm1)

end

/-! ## Stores to the output polynomial -/

/-- `a[j]`, with `rbp` = `a` and `rdi` = `j`. -/
theorem ea_aJ (s : State) {aP : Addr} {j : Nat} (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 j) :
    s.ea aJ = coeffAddr aP j := by
  simp only [State.ea, aJ, hbp, hdi]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ofNat64_succ {j : Nat} (_h : j + 1 < 2 ^ 64) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat64_toNat {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem offAdd (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- An offset of an offset of the working space. -/
theorem at_add (P : VG.Proof.MlDsa.X86_64.Sample.Sp) (a b : Nat) : P.at' a + BitVec.ofNat 64 b = P.at' (a + b) := VG.Proof.MlDsa.X86_64.Sample.offAdd _ _ _

theorem sx256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide

/-- `cmp rdi, 256`: CF is `rdi < 256`. -/
theorem cmpRdi_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 256)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [VG.Proof.MlDsa.X86_64.Sample.sx256, show (256 : BitVec 64).toNat = 256 from rfl]

/-- `add rsi, k; sub rcx, 1`: the step of a loop. -/
theorem step_ok (s : State) (k : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm k), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.gpr .rsi = s.gpr .rsi + k.signExtend 64 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop`. -/
section

/-!
# ML-DSA on x86-64: the loop of `vg_mldsa_rej_ntt_poly`

An iteration of the loop does what `rnStep` does to the coefficients sampled
so far, stored at `a` (`Stored`) and counted in `rdi` (`rnBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)

theorem bw32 (c : Byte) : (BitVec.setWidth 32 (BitVec.setWidth 64 c)).toNat = c.toNat := by
  rw [BitVec.toNat_setWidth, toNat_setWidth64_8, Nat.mod_eq_of_lt (by have := c.isLt; omega)]

/-- The value of the bytes `b₀, b₁, b₂`, as the code computes it. -/
def rnw (b₀ b₁ b₂ : Byte) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 b₂) &&& 127).rotateRight 16 +
    (BitVec.setWidth 32 (BitVec.setWidth 64 b₁)).rotateRight 24 + BitVec.setWidth 32 (BitVec.setWidth 64 b₀)

theorem rnw_toNat (b₀ b₁ b₂ : Byte) : (VG.Proof.MlDsa.X86_64.Sample.rnw b₀ b₁ b₂).toNat = rnZ b₀ b₁ b₂ := by
  have e2 : (BitVec.setWidth 32 (BitVec.setWidth 64 b₂) &&& 127).toNat = b₂.toNat % 128 := by
    rw [BitVec.toNat_and, VG.Proof.MlDsa.X86_64.Sample.bw32, show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h0 := b₀.isLt
  have h1 := b₁.isLt
  have h2 := Nat.mod_lt b₂.toNat (show 128 > 0 by decide)
  have r2 := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 b₂) &&& 127) (r := 16) (by decide)
    (by rw [e2]; omega)
  have r1 := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 b₁)) (r := 24) (by decide) (by rw [VG.Proof.MlDsa.X86_64.Sample.bw32]; omega)
  rw [e2] at r2
  rw [VG.Proof.MlDsa.X86_64.Sample.bw32] at r1
  rw [VG.Proof.MlDsa.X86_64.Sample.rnw, BitVec.toNat_add, BitVec.toNat_add, r2, r1, VG.Proof.MlDsa.X86_64.Sample.bw32, rnZ]
  rw [show 32 - 16 = 16 from rfl, show 32 - 24 = 8 from rfl]
  omega

theorem rnLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa (.block rnLoad) s fun s' =>
      (s'.gpr .r8 = BitVec.setWidth 64 (VG.Proof.MlDsa.X86_64.Sample.rnw (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
          (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rnLoad
  xrun [h0, h1, h2, VG.Proof.MlDsa.X86_64.Sample.sx256, VG.Proof.MlDsa.X86_64.Sample.rnw, show (256 : BitVec 64).toNat = 256 from rfl]

/-! ## A try -/

theorem rnCmp_ok (s : State) :
    WP isa (.block [.alu32 .cmp .r8 (.imm qImm)]) s fun s' =>
      s'.cf = some (decide (((s.gpr .r8).setWidth 32).toNat < q)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [show qImm.toNat = 8380417 from rfl]

theorem storeJ_ok (r : Reg) (s : State) {a : Addr} (ha : s.ea aJ = a) (hw : InRegions s.wr a 4) :
    WP isa (.block [.store32 aJ r, .alu .add .rdi (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) ∧ s'.gpr .rdi = s.gpr .rdi + 1) ∧ Keep [.rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [ha, hw]

/-- Each coefficient of the polynomial at `aP` lies in one of the writable
regions `wr`. -/
def CoeffsWr (wr : List Region) (aP : Addr) : Prop := ∀ i < 256, InRegions wr (coeffAddr aP i) 4

theorem CoeffsWr.of_mem {wr : List Region} {aP : Addr} (h : pR aP ∈ wr) : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr wr aP :=
  fun _ hi => ⟨_, h, coeff_contains _ hi⟩

/-- Storing the word `v` (less than `q`) as the next coefficient. -/
theorem store_next {s : State} {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length < 256) (hw : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP)
    (hst : VG.Proof.MlDsa.Sample.Stored s.mem aP L) (r : Reg) {v : BitVec 32} (hv : (s.gpr r).setWidth 32 = v) (hq : v.toNat < q) :
    WP isa (.block [.store32 aJ r, .alu .add .rdi (.imm 1)]) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (L ++ [Fin.ofNat q v.toNat]).length ∧
        VG.Proof.MlDsa.Sample.Stored s'.mem aP (L ++ [Fin.ofNat q v.toNat]) ∧ Frame [pR aP] s.mem s'.mem ∧ Keep [.rdi] s s' := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.storeJ_ok r s (VG.Proof.MlDsa.X86_64.Sample.ea_aJ s hbp hdi) (hw _ hL)) fun s' ⟨⟨hm, hdi'⟩, k⟩ => ?_
  have hz : zw (Fin.ofNat q v.toNat) = v := by
    apply BitVec.eq_of_toNat_eq
    rw [zw_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq]
  refine ⟨by rw [hdi', hdi, List.length_append, List.length_singleton]; exact VG.Proof.MlDsa.X86_64.Sample.ofNat64_succ (by omega), ?_,
    by rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hL), k⟩
  have := VG.Proof.MlDsa.Sample.stored_snoc hst hL (Fin.ofNat q v.toNat)
  rw [hz] at this
  rw [hm, hv]; exact this

/-- The hypotheses of a try. -/
structure TryPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length < 256
  wr : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP
  st : VG.Proof.MlDsa.Sample.Stored s.mem aP L

/-- The coefficients after a try of the value `v`. -/
def rnTryL (L : List Zq) (v : Nat) : List Zq := if v < q then L ++ [Fin.ofNat q v] else L

theorem rnTry_ok (s : State) {aP : Addr} {L : List Zq} (h : VG.Proof.MlDsa.X86_64.Sample.TryPre s aP L) :
    WP isa rnTry s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.rnTryL L ((s.gpr .r8).setWidth 32).toNat).length ∧
      VG.Proof.MlDsa.Sample.Stored s'.mem aP (VG.Proof.MlDsa.X86_64.Sample.rnTryL L ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] s.mem s'.mem ∧
      Keep [.rdi] s s' := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rnCmp_ok s) fun s1 ⟨hc, hm, hg, hrd, hwr⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg], hrd, hwr⟩
  refine WP.ite (decide (((s.gpr .r8).setWidth 32).toNat < q)) hc (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rw [VG.Proof.MlDsa.X86_64.Sample.rnTryL, ifT hb]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.store_next (s := s1) (by rw [hg, h.rbp]) (by rw [hg, h.rdi]) h.len (by rw [hwr]; exact h.wr)
      (by rw [hm]; exact h.st) .r8 (by rw [hg]) hb) fun s2 ⟨hdi, hst, hf, k2⟩ =>
      ⟨hdi, hst, by rw [← hm]; exact hf, (k1.trans k2).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hb
    rw [VG.Proof.MlDsa.X86_64.Sample.rnTryL, ifF hb]
    exact WP.block_nil ⟨by rw [hg, h.rdi], by rw [hm]; exact h.st, by rw [hm]; exact Frame.refl _ _,
      k1.mono (by simp)⟩

/-! ## An iteration -/

/-- The coefficients after an iteration, from the value `v`. -/
def rnMid (L : List Zq) (v : Nat) : List Zq := if L.length < 256 then VG.Proof.MlDsa.X86_64.Sample.rnTryL L v else L

theorem rnStep_eq (L : List Zq) (b₀ b₁ b₂ : Byte) : rnStep L b₀ b₁ b₂ = VG.Proof.MlDsa.X86_64.Sample.rnMid L (VG.Proof.MlDsa.X86_64.Sample.rnw b₀ b₁ b₂).toNat := by
  rw [rnStep, VG.Proof.MlDsa.X86_64.Sample.rnMid, VG.Proof.MlDsa.X86_64.Sample.rnw_toNat]; rfl

/-- The try, if `j < 256`. -/
theorem rnMid_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP)
    (hst : VG.Proof.MlDsa.Sample.Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) :
    WP isa (.ite .b rnTry (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.rnMid L ((s.gpr .r8).setWidth 32).toNat).length ∧
        VG.Proof.MlDsa.Sample.Stored s'.mem aP (VG.Proof.MlDsa.X86_64.Sample.rnMid L ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] s.mem s'.mem ∧
        Keep [.rdi] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, VG.Proof.MlDsa.X86_64.Sample.ofNat64_toNat (by omega)]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rw [VG.Proof.MlDsa.X86_64.Sample.rnMid, ifT hb]
    exact VG.Proof.MlDsa.X86_64.Sample.rnTry_ok s ⟨hbp, hdi, hb, hw, hst⟩
  · simp only [decide_eq_false_iff_not] at hb
    rw [VG.Proof.MlDsa.X86_64.Sample.rnMid, ifF hb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩

theorem sw32_64 (x : BitVec 32) : (BitVec.setWidth 64 x).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, toNat_setWidth64, Nat.mod_eq_of_lt x.isLt]

theorem sx3 : BitVec.signExtend 64 (3 : BitVec 32) = BitVec.ofNat 64 3 := by decide

/-- An iteration: what `rnStep` does to the coefficients `L`. -/
theorem rnBody_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP)
    (hst : VG.Proof.MlDsa.Sample.Stored s.mem aP L) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa rnBody s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (rnStep L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))).length ∧
      VG.Proof.MlDsa.Sample.Stored s'.mem aP (rnStep L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := by
  rw [VG.Proof.MlDsa.X86_64.Sample.rnStep_eq]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rnLoad_ok s h0 h1 h2) fun s1 ⟨⟨h8, hcf, hm1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rnMid_ok s1 (aP := aP) (L := L) (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi]) hL
    (by rw [k1.2.2]; exact hw) (by rw [hm1]; exact hst) (by rw [hcf, hdi1])) fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_)
  rw [h8, VG.Proof.MlDsa.X86_64.Sample.sw32_64] at hdi3 hst3
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.step_ok s3 3) fun s4 ⟨⟨hsi4, hcx4, hz4, hm4⟩, k4⟩ => ?_
  have hsi3 : s3.gpr .rsi = s.gpr .rsi := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  have hcx3 : s3.gpr .rcx = s.gpr .rcx := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  exact ⟨by rw [k4.gpr (by decide), hdi3], by rw [hm4]; exact hst3, by rw [hm4, ← hm1]; exact hf3,
    by rw [hsi4, hsi3, VG.Proof.MlDsa.X86_64.Sample.sx3], by rw [hcx4, hcx3], by rw [hz4, hcx3], ((k1.trans k3).trans k4).mono (by simp)⟩

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop`. -/
section

/-!
# ML-DSA on x86-64: the loop of `vg_mldsa_rej_bounded_poly`

The coefficient of an accepted half-byte, computed without a branch (`rbVal`),
is the one of `CoeffFromHalfByte`, modulo `q` (`rbF_eq`, by evaluation on the
16 half-bytes); so a try does what `hbTry` does (`rbTry_ok`), and an iteration
what `rbStep` does (`rbBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt coeffFromHalfByte)

/-! ## The coefficient of a half-byte -/

/-- `x - s` if `s ≤ x`, as `csub s` computes it. -/
def csubF (s x : BitVec 32) : BitVec 32 :=
  x - s + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (x.toNat < s.toNat))) &&& s)

/-- `(η - x) mod q`, as `etaSub η` computes it. -/
def etaF (η x : BitVec 32) : BitVec 32 :=
  η - x + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (η.toNat < x.toNat))) &&& qImm)

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 32 → BitVec 32
  | 2, x => VG.Proof.MlDsa.X86_64.Sample.etaF 2 (VG.Proof.MlDsa.X86_64.Sample.csubF 5 (VG.Proof.MlDsa.X86_64.Sample.csubF 10 x))
  | _, x => VG.Proof.MlDsa.X86_64.Sample.etaF 4 x

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbB (η : Nat) : Nat := if η = 2 then 15 else 9

/-- The coefficient of an accepted half-byte. -/
def rbC (η b : Nat) : Int := if η = 2 then 2 - (b % 5 : Nat) else 4 - b

theorem coeffFromHalfByte_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    coeffFromHalfByte η b = if b < VG.Proof.MlDsa.X86_64.Sample.rbB η then some (VG.Proof.MlDsa.X86_64.Sample.rbC η b) else none := by
  rcases hη with rfl | rfl <;> simp [coeffFromHalfByte, VG.Proof.MlDsa.X86_64.Sample.rbB, VG.Proof.MlDsa.X86_64.Sample.rbC]

theorem rbF_eq2 : ∀ b < 15, VG.Proof.MlDsa.X86_64.Sample.rbF 2 (BitVec.ofNat 32 b) = zw (ofInt (VG.Proof.MlDsa.X86_64.Sample.rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, VG.Proof.MlDsa.X86_64.Sample.rbF 4 (BitVec.ofNat 32 b) = zw (ofInt (VG.Proof.MlDsa.X86_64.Sample.rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < VG.Proof.MlDsa.X86_64.Sample.rbB η) :
    VG.Proof.MlDsa.X86_64.Sample.rbF η (BitVec.ofNat 32 b) = zw (ofInt (VG.Proof.MlDsa.X86_64.Sample.rbC η b)) := by
  rcases hη with rfl | rfl
  · exact VG.Proof.MlDsa.X86_64.Sample.rbF_eq2 b hb
  · exact VG.Proof.MlDsa.X86_64.Sample.rbF_eq4 b hb

theorem rbBound_toNat {η : Nat} (hη : η = 2 ∨ η = 4) : (rbBound η).toNat = VG.Proof.MlDsa.X86_64.Sample.rbB η := by
  rcases hη with rfl | rfl <;> rfl

theorem hbTry_eq {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    hbTry η L b = if b < VG.Proof.MlDsa.X86_64.Sample.rbB η then L ++ [ofInt (VG.Proof.MlDsa.X86_64.Sample.rbC η b)] else L := by
  unfold hbTry
  rw [VG.Proof.MlDsa.X86_64.Sample.coeffFromHalfByte_eq hη]
  by_cases h : b < VG.Proof.MlDsa.X86_64.Sample.rbB η <;> simp [h]

theorem rbVal_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) :
    WP isa (.block (rbVal η)) s fun s' =>
      (s'.gpr .r8 = BitVec.setWidth 64 (VG.Proof.MlDsa.X86_64.Sample.rbF η ((s.gpr .rdx).setWidth 32)) ∧ s'.mem = s.mem) ∧
        Keep [.rdx, .r8] s s' := by
  rcases hη with rfl | rfl
  · refine WP.keep _ ?_ (by decide)
    simp only [rbVal, csub, etaSub, List.cons_append, List.nil_append]
    xrun
    all_goals rfl
  · refine WP.keep _ ?_ (by decide)
    simp only [rbVal, etaSub]
    xrun
    all_goals rfl

/-! ## A try -/

theorem rbCmp_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) :
    WP isa (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) s fun s' =>
      s'.cf = some (decide (((s.gpr .rdx).setWidth 32).toNat < VG.Proof.MlDsa.X86_64.Sample.rbB η)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [VG.Proof.MlDsa.X86_64.Sample.rbBound_toNat hη]

/-- Store the coefficient of the half-byte `b` in `rdx` if it is accepted. -/
theorem rbTry_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (h : VG.Proof.MlDsa.X86_64.Sample.TryPre s aP L)
    {b : Nat} (hb : b < 16) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (rbTry η) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (hbTry η L b).length ∧ VG.Proof.MlDsa.Sample.Stored s'.mem aP (hbTry η L b) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rdx, .r8, .rdi] s s' := by
  have hbn : ((s.gpr .rdx).setWidth 32).toNat = b := by rw [hdx, BitVec.toNat_ofNat]; omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rbCmp_ok hη s) fun s1 ⟨hc, hm, hg, hrd, hwr⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg], hrd, hwr⟩
  rw [hbn] at hc
  rw [VG.Proof.MlDsa.X86_64.Sample.hbTry_eq hη]
  refine WP.ite (decide (b < VG.Proof.MlDsa.X86_64.Sample.rbB η)) hc (fun hbb => ?_) (fun hbb => ?_)
  · simp only [decide_eq_true_eq] at hbb
    rw [ifT hbb, WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.rbVal_ok hη s1) fun s2 ⟨⟨h8, hm2⟩, k2⟩ => ?_
    have hv : VG.Proof.MlDsa.X86_64.Sample.rbF η ((s1.gpr .rdx).setWidth 32) = zw (ofInt (VG.Proof.MlDsa.X86_64.Sample.rbC η b)) := by rw [hg, hdx, VG.Proof.MlDsa.X86_64.Sample.rbF_eq hη hbb]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.store_next (s := s2) (aP := aP) (by rw [k2.gpr (by decide), hg, h.rbp])
      (by rw [k2.gpr (by decide), hg, h.rdi]) h.len (by rw [k2.2.2, hwr]; exact h.wr)
      (by rw [hm2, hm]; exact h.st) .r8 (v := zw (ofInt (VG.Proof.MlDsa.X86_64.Sample.rbC η b))) (by rw [h8, VG.Proof.MlDsa.X86_64.Sample.sw32_64, hv])
      (by rw [zw_toNat]; exact (ofInt (VG.Proof.MlDsa.X86_64.Sample.rbC η b)).isLt)) fun s3 ⟨hdi, hst, hf, k3⟩ => ?_
    rw [ofNat_zw] at hdi hst
    exact ⟨hdi, hst, by rw [← hm, ← hm2]; exact hf, ((k1.trans k2).trans k3).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hbb
    rw [ifF hbb]
    exact WP.block_nil ⟨by rw [hg, h.rdi], by rw [hm]; exact h.st, by rw [hm]; exact Frame.refl _ _,
      k1.mono (by simp)⟩

/-! ## An iteration -/

theorem rbLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) :
    WP isa (.block rbLoad) s fun s' =>
      (s'.gpr .rax = BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ∧
        (s'.gpr .rdx).setWidth 32 = BitVec.ofNat 32 ((s.mem (s.gpr .rsi)).toNat % 16) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rbLoad
  xrun [h0, VG.Proof.MlDsa.X86_64.Sample.sx256, show (256 : BitVec 64).toNat = 256 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, VG.Proof.MlDsa.X86_64.Sample.bw32, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ % 16) (by omega)]

theorem rbHi_ok (s : State) {z : Byte} (hax : s.gpr .rax = BitVec.setWidth 64 z) :
    WP isa (.block rbHi) s fun s' =>
      ((s'.gpr .rdx).setWidth 32 = BitVec.ofNat 32 (z.toNat / 16) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rbHi
  xrun [hax, VG.Proof.MlDsa.X86_64.Sample.sx256, show (256 : BitVec 64).toNat = 256 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [shr_toNat, VG.Proof.MlDsa.X86_64.Sample.bw32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 16) (by have := z.isLt; omega)]

/-- The coefficients after the second try, if `j < 256`. -/
def rbMid2 (η : Nat) (L : List Zq) (b : Nat) : List Zq := if L.length < 256 then hbTry η L b else L

/-- The coefficients after an iteration, from the byte `z`. -/
theorem rbStep_eq (η : Nat) (L : List Zq) (z : Byte) :
    rbStep η L z = if L.length < 256 then VG.Proof.MlDsa.X86_64.Sample.rbMid2 η (hbTry η L (z.toNat % 16)) (z.toNat / 16) else L := by
  rw [rbStep, VG.Proof.MlDsa.X86_64.Sample.rbMid2]

theorem hbTry_length_le {η : Nat} {L : List Zq} (hL : L.length < 256) (b : Nat) : (hbTry η L b).length ≤ 256 := by
  rw [hbTry_length]; have := VG.Proof.MlDsa.Sample.halfByteOk_le η b; omega

/-- The second try, if `j < 256`. -/
theorem rbMid2_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP)
    (hst : VG.Proof.MlDsa.Sample.Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) {b : Nat} (hb : b < 16)
    (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.ite .b (rbTry η) (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.rbMid2 η L b).length ∧ VG.Proof.MlDsa.Sample.Stored s'.mem aP (VG.Proof.MlDsa.X86_64.Sample.rbMid2 η L b) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rdx, .r8, .rdi] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, VG.Proof.MlDsa.X86_64.Sample.ofNat64_toNat (by omega)]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hbb => ?_) (fun hbb => ?_)
  · simp only [decide_eq_true_eq] at hbb
    rw [VG.Proof.MlDsa.X86_64.Sample.rbMid2, ifT hbb]
    exact VG.Proof.MlDsa.X86_64.Sample.rbTry_ok hη s ⟨hbp, hdi, hbb, hw, hst⟩ hb hdx
  · simp only [decide_eq_false_iff_not] at hbb
    rw [VG.Proof.MlDsa.X86_64.Sample.rbMid2, ifF hbb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩

/-- The two tries, if `j < 256`. -/
theorem rbMid_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP)
    (hst : VG.Proof.MlDsa.Sample.Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) {z : Byte}
    (hax : s.gpr .rax = BitVec.setWidth 64 z) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 (z.toNat % 16)) :
    WP isa (.ite .b (.seq (rbTry η) (.seq (.block rbHi) (.ite .b (rbTry η) (.block [])))) (.block [])) s
      fun s' => s'.gpr .rdi = BitVec.ofNat 64 (rbStep η L z).length ∧ VG.Proof.MlDsa.Sample.Stored s'.mem aP (rbStep η L z) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rax, .rdx, .r8, .rdi] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, VG.Proof.MlDsa.X86_64.Sample.ofNat64_toNat (by omega)]
  rw [VG.Proof.MlDsa.X86_64.Sample.rbStep_eq]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hbb => ?_) (fun hbb => ?_)
  · simp only [decide_eq_true_eq] at hbb
    rw [ifT hbb]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rbTry_ok hη s ⟨hbp, hdi, hbb, hw, hst⟩ (Nat.mod_lt _ (by decide)) hdx)
      fun s1 ⟨hdi1, hst1, hf1, k1⟩ => ?_)
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rbHi_ok s1 (z := z) (by rw [k1.gpr (by decide), hax]))
      fun s2 ⟨⟨hdx2, hcf2, hm2, hdi2⟩, k2⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.rbMid2_ok hη s2 (aP := aP) (L := hbTry η L (z.toNat % 16)) (by rw [k2.gpr (by decide), k1.gpr (by decide), hbp])
      (by rw [hdi2, hdi1]) (VG.Proof.MlDsa.X86_64.Sample.hbTry_length_le hbb _) (by rw [k2.2.2, k1.2.2]; exact hw) (by rw [hm2]; exact hst1)
      (by rw [hcf2, hdi2]) (by have := z.isLt; omega) hdx2) fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_
    exact ⟨hdi3, hst3, hf1.trans (by rw [← hm2]; exact hf3), ((k1.trans k2).trans k3).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hbb
    rw [ifF hbb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩

theorem sx1' : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide

/-- An iteration: what `rbStep` does to the coefficients `L`. -/
theorem rbBody_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP)
    (hst : VG.Proof.MlDsa.Sample.Stored s.mem aP L) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) :
    WP isa (rbBody η) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (rbStep η L (s.mem (s.gpr .rsi))).length ∧
      VG.Proof.MlDsa.Sample.Stored s'.mem aP (rbStep η L (s.mem (s.gpr .rsi))) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rbLoad_ok s h0) fun s1 ⟨⟨hax, hdx, hcf, hm1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.rbMid_ok hη s1 (aP := aP) (L := L) (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi])
    hL (by rw [k1.2.2]; exact hw) (by rw [hm1]; exact hst) (by rw [hcf, hdi1]) hax hdx)
    fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.step_ok s3 1) fun s4 ⟨⟨hsi4, hcx4, hz4, hm4⟩, k4⟩ => ?_
  have hsi3 : s3.gpr .rsi = s.gpr .rsi := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  have hcx3 : s3.gpr .rcx = s.gpr .rcx := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  exact ⟨by rw [k4.gpr (by decide), hdi3], by rw [hm4]; exact hst3, by rw [hm4, ← hm1]; exact hf3,
    by rw [hsi4, hsi3, VG.Proof.MlDsa.X86_64.Sample.sx1'], by rw [hcx4, hcx3], by rw [hz4, hcx3], ((k1.trans k3).trans k4).mono (by simp)⟩

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMaskLoop`. -/
section

/-!
# ML-DSA on x86-64: the loop of `vg_mldsa_expand_mask_poly`

Coefficient `k` of a group reads the 32-bit word at byte `⌊ck/8⌋` of the
group, whose bits from `ck mod 8` on are those of the output from bit `ci` on
(`word_bits`: only its first 3 bytes matter); it stores `γ₁` minus their low
`c` bits modulo `q` (`etaF_eq`) to `a[i]` (`emCoef_run`, `emCoef_val`). A
group stores 4 coefficients (`emBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt coeffAt)

/-! ## Values -/

/-- `(g - x) mod q`, computed with a mask from the borrow. -/
theorem etaF_eq {g x : BitVec 32} (hg : g.toNat < q) (hx : x.toNat < q + g.toNat) :
    VG.Proof.MlDsa.X86_64.Sample.etaF g x = zw (ofInt ((g.toNat : Int) - x.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat]
  simp only [ofInt, Fin.val_ofNat]
  simp only [q] at hg hx ⊢
  unfold VG.Proof.MlDsa.X86_64.Sample.etaF
  by_cases h : g.toNat < x.toNat
  · rw [decide_eq_true h, show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true) &&& qImm) = qImm by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show qImm.toNat = 8380417 from rfl]
    omega
  · rw [decide_eq_false h, show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false) &&& qImm) = 0 by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-- Bit `j` of a 32-bit little-endian word. -/
theorem readW32_getLsbD (m : Mem) (a : Addr) {j : Nat} (hj : j < 32) :
    (m.readW a 32).getLsbD j = (m (a + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [Mem.readW_byte m a (by omega), BitVec.getLsbD_extractLsb']
  simp only [show j % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-- The `c` bits from bit `sh` of the word at `a` are those of `X` from bit
`8o + sh`, if its first 3 bytes are those of `X` from byte `o`. -/
theorem word_bits (m : Mem) (a : Addr) (X : List Byte) {o sh c : Nat} (hc : sh + c ≤ 24)
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (o + b) 0) :
    (m.readW a 32).toNat / 2 ^ sh % 2 ^ c = leNat X / 2 ^ (8 * o + sh) % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < c
  · simp only [hj, decide_true, Bool.true_and]
    rw [← BitVec.getLsbD, VG.Proof.MlDsa.X86_64.Sample.readW32_getLsbD m a (j := j + sh) (by omega), hb ((j + sh) / 8) (by omega),
      testBit_leNat, show (j + (8 * o + sh)) / 8 = o + (j + sh) / 8 by omega,
      show (j + (8 * o + sh)) % 8 = (j + sh) % 8 by omega]
  · simp [hj]

/-! ## A coefficient -/

/-- The value stored for coefficient `i` of `c` bits from the output `X`. -/
abbrev emV (X : List Byte) (c i : Nat) : BitVec 32 :=
  zw (ofInt (((2 ^ (c - 1) : Nat) : Int) - (leNat X / 2 ^ (i * c) % 2 ^ c : Nat)))

theorem emCoef_run (c k : Nat) (hk : c * k % 8 < 8) (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) 4)
    (h1 : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (emCoef c k)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 (4 * k))
        (VG.Proof.MlDsa.X86_64.Sample.etaF (BitVec.ofNat 32 (2 ^ (c - 1)))
          (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) 32 >>> (c * k % 8) &&&
            BitVec.ofNat 32 (2 ^ c - 1)))) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by
    unfold writesOnly emCoef
    split <;> rfl)
  by_cases hs : c * k % 8 = 0
  · simp only [emCoef, hs, ite_true, List.nil_append, List.cons_append]
    xrun [h0, h1]
    rw [BitVec.ushiftRight_zero]; rfl
  · simp only [emCoef, hs, ite_false, List.cons_append, List.nil_append]
    xrun [h0, h1, show 1 ≤ c * k % 8 by omega, show c * k % 8 ≤ 31 by omega]
    rfl

/-- The widths of the coefficients. -/
def emOk (c : Nat) : Prop := c = 18 ∨ c = 20

/-- The value of a coefficient, from the word read and the output `X`. -/
theorem emCoef_val {c : Nat} (hc : VG.Proof.MlDsa.X86_64.Sample.emOk c) (m : Mem) (a : Addr) (X : List Byte) {g k : Nat}
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (c / 2 * g + c * k / 8 + b) 0) :
    VG.Proof.MlDsa.X86_64.Sample.etaF (BitVec.ofNat 32 (2 ^ (c - 1))) (m.readW a 32 >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)) =
      VG.Proof.MlDsa.X86_64.Sample.emV X c (4 * g + k) := by
  have hc' : c ≤ 20 := by rcases hc with rfl | rfl <;> omega
  have hsh : c * k % 8 + c ≤ 24 := by rcases hc with rfl | rfl <;> omega
  have e1 : (m.readW a 32 >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)).toNat =
      leNat X / 2 ^ ((4 * g + k) * c) % 2 ^ c := by
    rw [BitVec.toNat_and, shr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ c - 1) (by
      have : 2 ^ c ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hc'; omega), Nat.and_two_pow_sub_one_eq_mod,
      VG.Proof.MlDsa.X86_64.Sample.word_bits m a X hsh hb]
    have e : 8 * (c / 2 * g + c * k / 8) + c * k % 8 = (4 * g + k) * c := by
      rcases hc with rfl | rfl <;> omega
    rw [e]
  have e2 : (BitVec.ofNat 32 (2 ^ (c - 1))).toNat = 2 ^ (c - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have : 2 ^ (c - 1) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega); omega)]
  have hp : 2 ^ c = 2 * 2 ^ (c - 1) := by
    rw [← Nat.pow_succ']; congr 1; rcases hc with rfl | rfl <;> rfl
  rw [VG.Proof.MlDsa.X86_64.Sample.etaF_eq (by rw [e2]; rcases hc with rfl | rfl <;> decide) (by
    rw [e1, e2]; have := Nat.mod_lt (leNat X / 2 ^ ((4 * g + k) * c)) (Nat.two_pow_pos c)
    have : 2 ^ (c - 1) < q := by rcases hc with rfl | rfl <;> decide
    omega), e1, e2]

/-! ## A group of 4 coefficients -/

theorem emOk_le {c : Nat} (hc : VG.Proof.MlDsa.X86_64.Sample.emOk c) : c / 2 * 63 + c * 3 / 8 ≤ 637 := by rcases hc with rfl | rfl <;> decide

/-- The facts a group needs. -/
structure GPre (c : Nat) (X : List Byte) (out aP : Addr) (g : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = aP + BitVec.ofNat 64 (16 * g)
  g_lt : g < 64
  bytes : ∀ j < 640, s.mem (out + BitVec.ofNat 64 j) = X.getD j 0
  rd : ∀ j ≤ 637, InRegions (s.rd ++ s.wr) (out + BitVec.ofNat 64 j) 4
  wr : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  apart : ∀ j < 640, ¬ (pR aP).Contains (out + BitVec.ofNat 64 j) 1

/-- The 4 coefficients of group `g`. -/
theorem emGroup_ok {c : Nat} (hc : VG.Proof.MlDsa.X86_64.Sample.emOk c) {X : List Byte} {out aP : Addr} {g : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sample.GPre c X out aP g s) :
    WP isa (.block ((List.range 4).flatMap (emCoef c))) s fun s' =>
      Keep [.rax, .rdx] s s' ∧ Frame [pR aP] s.mem s'.mem ∧
        (∀ k < 4, coeffAt s'.mem aP (4 * g + k) = VG.Proof.MlDsa.X86_64.Sample.emV X c (4 * g + k)) ∧
        (∀ i < 256, (i < 4 * g ∨ 4 * g + 4 ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i) := by
  have hg := h.g_lt
  have hle := VG.Proof.MlDsa.X86_64.Sample.emOk_le hc
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k s' => Keep [.rax, .rdx] s s' ∧
      Frame [pR aP] s.mem s'.mem ∧ (∀ j < k, coeffAt s'.mem aP (4 * g + j) = VG.Proof.MlDsa.X86_64.Sample.emV X c (4 * g + j)) ∧
      (∀ i < 256, (i < 4 * g ∨ 4 * g + k ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i))
    (fun k s' hk ⟨k', hf, hst, hsame⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩) fun s' h => h
  have hsi : s'.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * g) := by rw [k'.gpr (by decide), h.rsi]
  have hdi : s'.gpr .rdi = aP + BitVec.ofNat 64 (16 * g) := by rw [k'.gpr (by decide), h.rdi]
  have ha : s'.gpr .rdi + BitVec.ofNat 64 (4 * k) = coeffAddr aP (4 * g + k) := by
    rw [hdi, VG.Proof.MlDsa.X86_64.Sample.offAdd]; congr 2; omega
  have hr : s'.gpr .rsi + BitVec.ofNat 64 (c * k / 8) = out + BitVec.ofNat 64 (c / 2 * g + c * k / 8) := by
    rw [hsi, VG.Proof.MlDsa.X86_64.Sample.offAdd]
  have hkk : c * k / 8 ≤ c * 3 / 8 := Nat.div_le_div_right (Nat.mul_le_mul_left c (by omega))
  have hg' : c / 2 * g ≤ c / 2 * 63 := Nat.mul_le_mul_left _ (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.emCoef_run c k (by omega) s' (by rw [hr, k'.2.1, k'.2.2]; exact h.rd _ (by omega))
    (by rw [ha, k'.2.2]; exact h.wr _ (by omega))) fun s'' ⟨hm, k''⟩ => ?_
  have hv := VG.Proof.MlDsa.X86_64.Sample.emCoef_val hc s'.mem (s'.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) X (g := g) (k := k) (fun b hb => by
    rw [hr, VG.Proof.MlDsa.X86_64.Sample.offAdd, hf _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.apart _ (by omega)]
    exact h.bytes _ (by omega))
  rw [ha, hv] at hm
  refine ⟨k'.trans k'' |>.mono (by simp), ?_, fun j hj => ?_, fun i hi hi' => ?_⟩
  · rw [hm]; exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by omega))
  · rw [hm, coeffAt_writeW _ _ (by omega) (by omega)]
    by_cases e : j = k
    · subst e; rw [ifT rfl]
    · rw [ifF (by omega)]; exact hst j (by omega)
  · rw [hm, coeffAt_writeW _ _ hi (by omega), ifF (by omega)]
    exact hsame i hi (by omega)

theorem sxHalf {c : Nat} (hc : VG.Proof.MlDsa.X86_64.Sample.emOk c) : BitVec.signExtend 64 (BitVec.ofNat 32 (c / 2)) = BitVec.ofNat 64 (c / 2) := by
  rcases hc with rfl | rfl <;> decide

/-- An iteration: a group, and the pointers and counter advanced. -/
theorem emBody_ok {c : Nat} (hc : VG.Proof.MlDsa.X86_64.Sample.emOk c) {X : List Byte} {out aP : Addr} {g : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sample.GPre c X out aP g s) :
    WP isa (.block (emBody c)) s fun s' =>
      Keep [.rax, .rdx, .rsi, .rdi, .rcx] s s' ∧ Frame [pR aP] s.mem s'.mem ∧
        (∀ k < 4, coeffAt s'.mem aP (4 * g + k) = VG.Proof.MlDsa.X86_64.Sample.emV X c (4 * g + k)) ∧
        (∀ i < 256, (i < 4 * g ∨ 4 * g + 4 ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i) ∧
        s'.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * (g + 1)) ∧ s'.gpr .rdi = aP + BitVec.ofNat 64 (16 * (g + 1)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  unfold emBody
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.emGroup_ok hc h) fun s1 ⟨k1, hf1, hst1, hsame1⟩ => ?_
  refine WP.mono (WP.keep [.rsi, .rdi, .rcx] (Q := fun s' => s'.mem = s1.mem ∧
      s'.gpr .rsi = s1.gpr .rsi + BitVec.ofNat 64 (c / 2) ∧ s'.gpr .rdi = s1.gpr .rdi + BitVec.ofNat 64 16 ∧
      s'.gpr .rcx = s1.gpr .rcx - 1 ∧ s'.zf = some (s1.gpr .rcx - 1 == 0)) (by xrun [VG.Proof.MlDsa.X86_64.Sample.sxHalf hc]; rfl)
    (by rfl)) fun s2 ⟨⟨hm2, hsi2, hdi2, hcx2, hz2⟩, k2⟩ => ?_
  have hcx1 : s1.gpr .rcx = s.gpr .rcx := k1.gpr (by decide)
  refine ⟨k1.trans k2 |>.mono (by simp), by rw [hm2]; exact hf1, fun k hk => by rw [hm2]; exact hst1 k hk,
    fun i hi hi' => by rw [hm2]; exact hsame1 i hi hi', ?_, ?_, by rw [hcx2, hcx1], by rw [hz2, hcx1]⟩
  · rw [hsi2, k1.gpr (by decide), h.rsi, VG.Proof.MlDsa.X86_64.Sample.offAdd, Nat.mul_succ]
  · rw [hdi2, k1.gpr (by decide), h.rdi, VG.Proof.MlDsa.X86_64.Sample.offAdd, Nat.mul_succ]

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallLoop`. -/
section

/-!
# ML-DSA on x86-64: the loops of `vg_mldsa_sample_in_ball`

The polynomial `c` is kept in memory as the words that represent its
coefficients modulo `q` (`CStored`); the first loop zeroes it (`bZero_ok`),
and an iteration of the second does what `bStep` does to it and to `i` (in
`rdi`), with the sign bits not yet used in `r9` (`bBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt coeffAt IPoly n)
open VG.Impl.MlKem.X86_64 (at_)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (s₀ : State) (aP : Addr) (k : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = aP + BitVec.ofNat 64 (4 * k)
  rax : s.gpr .rax = 0
  keep : Keep [.rax, .rdi, .rcx] s₀ s
  frame : Frame [pR aP] s₀.mem s.mem
  zero : ∀ j < k, coeffAt s.mem aP j = 0

theorem zStep_ok (s : State) {a : Addr} (ha : s.gpr .rdi = a) (hw : InRegions s.wr a 4) :
    WP isa (.block [.store32 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a ((s.gpr .rax).setWidth 32) ∧ s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 4 ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [ha, hw]
  rfl

/-- The zeroing loop: the 256 coefficients at `rbp` set to 0. -/
theorem bZero_ok (s₀ : State) {aP : Addr} (hbp : s₀.gpr .rbp = aP) (hw : pR aP ∈ s₀.wr) :
    WP isa bZero s₀ fun s => Keep [.rax, .rdi, .rcx] s₀ s ∧ Frame [pR aP] s₀.mem s.mem ∧
      VG.Proof.MlDsa.X86_64.Sample.CStored s.mem aP (Vector.replicate n 0) := by
  refine WP.seq (WP.mono (WP.keep [.rax, .rdi] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .rax = 0 ∧
      s.gpr .rdi = aP) (by xrun [hbp]) (by decide)) fun s1 ⟨⟨hm1, hax, hdi⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s => s.mem = s1.mem ∧ s.gpr .rcx = BitVec.ofNat 64 256)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_)
  refine wp_countdown (N := 256) (by decide) (by decide) (VG.Proof.MlDsa.X86_64.Sample.ZAt s₀ aP) (fun k hk s hI _ => ?_)
    (fun s h => ⟨h.keep, h.frame, fun j hj => ?_⟩)
    ⟨by rw [k2.gpr (by decide), hdi]; simp, by rw [k2.gpr (by decide), hax], (k1.trans k2).mono (by simp),
      by rw [hm2, hm1]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩ hcx
  · have ha : s.gpr .rdi = coeffAddr aP k := by rw [hI.rdi]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.zStep_ok s ha (by rw [hI.keep.2.2]; exact ⟨_, hw, coeff_contains _ hk⟩))
      fun s' ⟨⟨hm, hdi', hcx', hz⟩, k'⟩ => ⟨⟨?_, by rw [k'.gpr (by decide), hI.rax], hI.keep.trans k' |>.mono (by simp),
        ?_, fun j hj => ?_⟩, hcx', hz⟩
    · rw [hdi', hI.rdi, VG.Proof.MlDsa.X86_64.Sample.offAdd, Nat.mul_succ]
    · rw [hm]; exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk)
    · rw [hm, coeffAt_writeW _ _ (by omega) hk, hI.rax]
      by_cases e : k = j
      · rw [ifT e]; rfl
      · rw [ifF e]; exact hI.zero j (by omega)
  · rw [h.zero j hj, getElem!_pos _ j (by simp only [n]; omega), Vector.getElem_replicate]
    rfl

/-! ## Setting a coefficient -/

theorem and1_beq (x : BitVec 64) : ((x &&& 1) == 0) = !x.getLsbD 0 := by
  have h1 : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h2 : x.getLsbD 0 = decide (x.toNat % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
    by_cases h : x.toNat % 2 = 1 <;> simp [h]
  rw [h2]
  by_cases h : x.toNat % 2 = 1
  · simp only [h, decide_true, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega
  · simp only [h, decide_false, Bool.not_false, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h1]; simp; omega

theorem ea_cJ (s : State) {aP : Addr} {j : Nat} (hbp : s.gpr .rbp = aP) (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    s.ea cJ = coeffAddr aP j := by
  simp only [State.ea, cJ, hbp, hax]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem bSet1_ok (s : State) {a b : Addr} (hb : s.ea cJ = b) (ha : s.ea aJ = a)
    (hr : InRegions (s.rd ++ s.wr) b 4) (hw : InRegions s.wr a 4) :
    WP isa (.block [.mov32 .rdx (.mem cJ), .store32 aJ .rdx, .alu .test .r9 (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a (s.mem.readW b 32) ∧ s'.zf = some ((s.gpr .r9 &&& 1) == 0) ∧
        s'.gpr .r9 = s.gpr .r9) ∧ Keep [.rdx, .r9] s s' := by
  refine WP.keep _ ?_ (by rfl)
  have ha' : (s.setReg .rdx (BitVec.setWidth 64 (s.mem.readW b 32))).ea aJ = a := by
    rw [← ha]; rfl
  xrun [hb, hr, hw, ha', VG.Proof.MlDsa.X86_64.Sample.sw32_64]

theorem bSet3_ok (s : State) {b : Addr} (hb : s.ea cJ = b) (hw : InRegions s.wr b 4) :
    WP isa (.block [.store32 cJ .rdx, .shift .shr .r9 1, .alu .add .rdi (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW b ((s.gpr .rdx).setWidth 32) ∧ s'.gpr .r9 = s.gpr .r9 >>> 1 ∧
        s'.gpr .rdi = s.gpr .rdi + 1) ∧ Keep [.r9, .rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hb, hw]

/-- The word of the sign: 1, or `q - 1` for -1. -/
theorem sgn_word (b : Bool) : (if b then (qImm - 1 : BitVec 32) else 1) = zw (ofInt (if b then -1 else 1)) := by
  cases b <;> decide

theorem movRdx_ok (s : State) (v : BitVec 32) :
    WP isa (.block [.mov32 .rdx (.imm v)]) s fun s' => (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = v) ∧
      Keep [.rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [VG.Proof.MlDsa.X86_64.Sample.sw32_64]

/-- The word of the sign `b`. -/
theorem bSign_ok (s : State) (b : Bool) (hz : s.zf = some (!b)) :
    WP isa (.ite .e (.block [.mov32 .rdx (.imm 1)]) (.block [.mov32 .rdx (.imm (qImm - 1))])) s fun s' =>
      (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = (if b then qImm - 1 else 1)) ∧ Keep [.rdx] s s' := by
  cases b
  · exact WP.ite true hz (fun _ => VG.Proof.MlDsa.X86_64.Sample.movRdx_ok s 1) (fun h => absurd h (by decide))
  · exact WP.ite false hz (fun h => absurd h (by decide)) (fun _ => VG.Proof.MlDsa.X86_64.Sample.movRdx_ok s (qImm - 1))

/-- `c[i] ← c[j]`, `c[j] ← ±1` (with the sign bit 0 of `r9`), `i` incremented. -/
theorem bSet_ok (s : State) {aP : Addr} {c : IPoly} {i j : Nat} (hij : j ≤ i) (hi : i < 256)
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hax : s.gpr .rax = BitVec.ofNat 64 j)
    (hw : pR aP ∈ s.wr) (hrd : pR aP ∈ s.rd ++ s.wr) (hst : VG.Proof.MlDsa.X86_64.Sample.CStored s.mem aP c) :
    WP isa bSet s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (i + 1) ∧
      VG.Proof.MlDsa.X86_64.Sample.CStored s'.mem aP ((c.set! i c[j]!).set! j (if (s.gpr .r9).getLsbD 0 then -1 else 1)) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .r9 = s.gpr .r9 >>> 1 ∧ Keep [.rdx, .r9, .rdi] s s' := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.bSet1_ok s (VG.Proof.MlDsa.X86_64.Sample.ea_cJ s hbp hax) (VG.Proof.MlDsa.X86_64.Sample.ea_aJ s hbp hdi) ⟨_, hrd, coeff_contains _ (by omega)⟩
    ⟨_, hw, coeff_contains _ hi⟩) fun s1 ⟨⟨hm1, hz1, h91⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.bSign_ok s1 ((s.gpr .r9).getLsbD 0) (by rw [hz1, VG.Proof.MlDsa.X86_64.Sample.and1_beq]))
    fun s2 ⟨⟨hm2, hdx2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.bSet3_ok s2 (b := coeffAddr aP j) (VG.Proof.MlDsa.X86_64.Sample.ea_cJ s2 (by rw [k12.gpr (by decide), hbp])
    (by rw [k12.gpr (by decide), hax])) (by rw [k12.2.2]; exact ⟨_, hw, coeff_contains _ (by omega)⟩))
    fun s3 ⟨⟨hm3, h93, hdi3⟩, k3⟩ => ⟨?_, fun k hk => ?_, ?_, ?_, (k12.trans k3).mono (by simp)⟩
  · rw [hdi3, k12.gpr (by decide), hdi]; exact VG.Proof.MlDsa.X86_64.Sample.ofNat64_succ (by omega)
  · rw [hm3, hm2, hm1, hdx2, coeffAt_writeW _ _ hk (by omega), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega), ipoly_set!_get _ _ (by simp only [n]; omega)]
    by_cases ejk : j = k
    · subst ejk; rw [ifT rfl, ifT rfl, VG.Proof.MlDsa.X86_64.Sample.sgn_word]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : i = k
      · subst eik; rw [ifT rfl, ifT rfl, ← coeffAt_eq, hst j (by omega)]
      · rw [ifF eik, ifF eik]; exact hst k hk
  · rw [hm3, hm2, hm1]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (by omega))
  · rw [h93, k2.gpr (by decide), h91]

/-! ## An iteration -/

theorem bLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) :
    WP isa (.block [.movzx8 .rax (at_ .rsi 0), .alu .cmp .rdi (.reg .rax)]) s fun s' =>
      (s'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rsi)).toNat ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < (s.mem (s.gpr .rsi)).toNat)) ∧ s'.mem = s.mem ∧
        s'.gpr .rdi = s.gpr .rdi) ∧ Keep [.rax, .rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  have e : BitVec.setWidth 64 (s.mem (s.gpr .rsi)) = BitVec.ofNat 64 (s.mem (s.gpr .rsi)).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_setWidth64_8, BitVec.toNat_ofNat]; have := (s.mem (s.gpr .rsi)).isLt; omega
  xrun [h0, e]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .rsi)).isLt; omega)]

/-- The try of the byte at `rsi`, if `i < 256`. -/
theorem bMid_ok (s : State) {aP : Addr} {c : IPoly} {i : Nat} {τ : Nat} {h : Array Bool}
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hi : i ≤ 256) (hw : pR aP ∈ s.wr)
    (hrd : pR aP ∈ s.rd ++ s.wr) (hst : VG.Proof.MlDsa.X86_64.Sample.CStored s.mem aP c) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (hsg : i < 256 → (s.gpr .r9).getLsbD 0 = h.getD (i + τ - 256) false)
    (hcf : s.cf = some (decide (i < 256))) :
    WP isa (.ite .b bTry (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 ∧
      VG.Proof.MlDsa.X86_64.Sample.CStored s'.mem aP (bStep τ h (c, i) (s.mem (s.gpr .rsi))).1 ∧ Frame [pR aP] s.mem s'.mem ∧
      s'.gpr .r9 = (if (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 = i then s.gpr .r9 else s.gpr .r9 >>> 1) ∧
      Keep [.rax, .rdx, .r9, .rdi] s s' := by
  refine WP.ite (decide (i < 256)) hcf (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    have hl : (s.gpr .rdi).toNat = i := by rw [hdi, VG.Proof.MlDsa.X86_64.Sample.ofNat64_toNat (by omega)]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.bLoad_ok s h0) fun s1 ⟨⟨hax, hcf1, hm1, hdi1⟩, k1⟩ => ?_)
    rw [hl] at hcf1
    refine WP.ite (decide (i < (s.mem (s.gpr .rsi)).toNat)) hcf1 (fun hj => ?_) (fun hj => ?_)
    · simp only [decide_eq_true_eq] at hj
      have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) = (c, i) := by
        unfold bStep; rw [ifT (show (c, i).2 < n from hb), ifT hj]
      rw [e]
      exact WP.block_nil ⟨by rw [hdi1, hdi], by rw [hm1]; exact hst, by rw [hm1]; exact Frame.refl _ _,
        by rw [ifT rfl, k1.gpr (by decide)], k1.mono (by simp)⟩
    · simp only [decide_eq_false_iff_not] at hj
      have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) =
          ((c.set! i c[(s.mem (s.gpr .rsi)).toNat]!).set! (s.mem (s.gpr .rsi)).toNat
            (if h.getD (i + τ - 256) false then -1 else 1), i + 1) := by
        unfold bStep; rw [ifT (show (c, i).2 < n from hb), ifF hj]
      rw [e, ← hsg hb]
      have h91 : s1.gpr .r9 = s.gpr .r9 := k1.gpr (by decide)
      refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.bSet_ok s1 (aP := aP) (c := c) (by omega) hb (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi]) hax
        (by rw [k1.2.2]; exact hw) (by rw [k1.2.1, k1.2.2]; exact hrd) (by rw [hm1]; exact hst))
        fun s2 ⟨hdi2, hst2, hf2, h92, k2⟩ => ⟨hdi2, by rw [h91] at hst2; exact hst2,
          by rw [← hm1]; exact hf2, by rw [ifF (by omega), h92, h91], (k1.trans k2).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hb
    have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) = (c, i) := by
      unfold bStep; rw [ifF (show ¬ (c, i).2 < n from hb)]
    rw [e]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, by rw [ifT rfl], Keep.refl _ _⟩

/-- An iteration: what `bStep` does to the polynomial and `i`. -/
theorem bBody_ok (s : State) {aP : Addr} {c : IPoly} {i : Nat} {τ : Nat} {h : Array Bool}
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hi : i ≤ 256) (hw : pR aP ∈ s.wr)
    (hrd : pR aP ∈ s.rd ++ s.wr) (hst : VG.Proof.MlDsa.X86_64.Sample.CStored s.mem aP c) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (hsg : i < 256 → (s.gpr .r9).getLsbD 0 = h.getD (i + τ - 256) false) :
    WP isa bBody s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 ∧
      VG.Proof.MlDsa.X86_64.Sample.CStored s'.mem aP (bStep τ h (c, i) (s.mem (s.gpr .rsi))).1 ∧ Frame [pR aP] s.mem s'.mem ∧
      s'.gpr .r9 = (if (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 = i then s.gpr .r9 else s.gpr .r9 >>> 1) ∧
      s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r9, .rdi, .rsi, .rcx] s s' := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.cmpRdi_ok s) fun s1 ⟨hcf1, hm1, hg1, hrd1, hwr1⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg1], hrd1, hwr1⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.bMid_ok s1 (aP := aP) (τ := τ) (h := h) (c := c) (by rw [hg1, hbp]) (by rw [hg1, hdi]) hi
    (by rw [hwr1]; exact hw) (by rw [hrd1, hwr1]; exact hrd) (by rw [hm1]; exact hst)
    (by rw [hrd1, hwr1, hg1]; exact h0) (by rw [hg1]; exact hsg)
    (by rw [hcf1, hdi, VG.Proof.MlDsa.X86_64.Sample.ofNat64_toNat (by omega)])) fun s2 ⟨hdi2, hst2, hf2, h92, k2⟩ => ?_)
  rw [hm1, hg1] at hdi2 hst2 h92
  rw [hm1] at hf2
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.step_ok s2 1) fun s3 ⟨⟨hsi3, hcx3, hz3, hm3⟩, k3⟩ => ?_
  have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hg1]
  have hcx2 : s2.gpr .rcx = s.gpr .rcx := by rw [k2.gpr (by decide), hg1]
  exact ⟨by rw [k3.gpr (by decide), hdi2], by rw [hm3]; exact hst2, by rw [hm3]; exact hf2,
    by rw [k3.gpr (by decide), h92], by rw [hsi3, hsi2, VG.Proof.MlDsa.X86_64.Sample.sx1'], by rw [hcx3, hcx2], by rw [hz3, hcx2],
    ((k1.trans k2).trans k3).mono (by simp)⟩

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`G(ρ, 1008)` (`J6`), and the loop, iteration `t` of which starts from `LAt σ
t` with the coefficients `rnFold` samples from the first `3t` bytes of output
stored.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mldsa_rej_ntt_poly(seed = rdi, a = rsi, scratch = rdx) -> eax`, with
16 bytes of stack below `rsp`. -/
def rnK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 34⟩] ∧ s.wr = [pR (s.gpr .rsi), ⟨s.gpr .rdx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 34⟩ (pR (s.gpr .rsi)) ∧ Region.Disjoint ⟨s.gpr .rdi, 34⟩ ⟨s.gpr .rdx, 2048⟩ ∧
    (pR (s.gpr .rsi)).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rsi)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧ (s.gpr .rdx).toNat + 2048 ≤ 2 ^ 64
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256 then 1 else 0) ∧
      ((rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256 →
        PolyIs s'.mem (s.gpr .rsi) (VG.Proof.MlDsa.Sample.toPoly (rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .rdi) 34) 1008))))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rdi) 34 = bytesAt s₂.mem (s₂.gpr .rdi) 34

namespace RejNtt

/-- The call. -/
abbrev spOf (σ : State) : VG.Proof.MlDsa.X86_64.Sample.Sp := ⟨σ.gpr .rdi, 34, σ.gpr .rdx, σ.gpr .rsi, 0⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 34

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := VG.Spec.MlDsa.G (VG.Proof.MlDsa.X86_64.Sample.RejNtt.B σ) 1008

section
variable {σ : State} (hp : rnK.pre σ)
include hp

theorem spOk : VG.Proof.MlDsa.X86_64.Sample.SpOk (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2, by show (34 : Nat) < 2 ^ 64; decide⟩

omit hp in
theorem sx34 : BitVec.signExtend 64 (34 : BitVec 32) = BitVec.ofNat 64 34 := by decide

theorem pro_ok : WP isa (.block (VG.Impl.MlDsa.X86_64.Sample.pro .rdx .rsi (.imm 0) (.imm 34))) σ (VG.Proof.MlDsa.X86_64.Sample.J0 (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rdx ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = 0 ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 34)
    (by unfold VG.Impl.MlDsa.X86_64.Sample.pro; xrun [VG.Proof.MlDsa.X86_64.Sample.inScrσ (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp) (a := 2024) (n := 8) (by omega),
      VG.Proof.MlDsa.X86_64.Sample.inScrσ (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp) (a := 2032) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Sample.inScrσ (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp) (a := 2040) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Sample.RejNtt.sx34])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ => VG.Proof.MlDsa.X86_64.Sample.pro_J0 hm hbx hbp h12 hcx h8 k

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rnFold [] ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ).take (3 * t))

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840) 1008 = VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ
  rsi : s.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840 + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (336 - t)
  stored : VG.Proof.MlDsa.Sample.Stored s.mem (σ.gpr .rsi) (VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ t)

omit hp in
theorem X_length : (VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ).length = 1008 := VG.Proof.MlDsa.Sample.G_length _ _

omit hp in
theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

omit hp in
theorem out_byte {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ t s) {k : Nat} (hk : 3 * t + k < 1008) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 k) = (VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ).getD (3 * t + k) 0 := by
  have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
  rw [MlKem.bytesAt_getD _ _ hk] at this
  rw [h.rsi, VG.Proof.MlDsa.X86_64.Sample.offAdd]; exact this

theorem lat_regions {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ t s) {k : Nat} (hk : 3 * t + k < 1008) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 k) 1 := by
  rw [h.rsi, VG.Proof.MlDsa.X86_64.Sample.at_add, VG.Proof.MlDsa.X86_64.Sample.at_add]; exact VG.Proof.MlDsa.X86_64.Sample.inScrRd (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp) h.env (by omega)

omit hp in
theorem Lt_length_le (t : Nat) : (VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- An iteration, from `LAt`. -/
theorem lat_step {t : Nat} {s : State} (ht : t < 336) (h : VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ t s) :
    WP isa rnBody s fun s' => VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (336 - t) - 1 == 0) := by
  have hw : pR (σ.gpr .rsi) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.rnBody_ok s (aP := σ.gpr .rsi) h.env.rbp h.rdi (VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt_length_le t) (.of_mem hw) h.stored
    (by simpa using VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_regions hp h (k := 0) (by omega)) (VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_regions hp h (by omega))
    (VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_regions hp h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := VG.Proof.MlDsa.X86_64.Sample.RejNtt.out_byte h (k := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  have ht3 : VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ (t + 1) = rnStep (VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ t) ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ).getD (3 * t) 0) ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ).getD (3 * t + 1) 0)
      ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ).getD (3 * t + 2) 0) := by
    simp only [VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt]
    rw [show 3 * (t + 1) = 3 * t + 3 by omega, VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [VG.Proof.MlDsa.X86_64.Sample.RejNtt.X_length]; omega),
      rnFold_snoc _ (by rw [List.length_take, VG.Proof.MlDsa.X86_64.Sample.RejNtt.X_length]; omega)]
  rw [e0, VG.Proof.MlDsa.X86_64.Sample.RejNtt.out_byte h (k := 1) (by omega), VG.Proof.MlDsa.X86_64.Sample.RejNtt.out_byte h (k := 2) (by omega), ← ht3] at hdi hst
  have hp' := VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' k) 64 = s.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (VG.Proof.MlDsa.X86_64.Sample.a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (VG.Proof.MlDsa.X86_64.Sample.r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (VG.Proof.MlDsa.X86_64.Sample.a_scr' hp' (a := 840) (n := 1008) (by omega)).symm)
      (by omega)]; exact h.out,
    by rw [hsi, h.rsi, VG.Proof.MlDsa.X86_64.Sample.offAdd, show 3 * (t + 1) = 3 * t + 3 by omega],
    hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩

omit hp in
theorem lat0 {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J6 168 1008 (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ s' ∧ bytesAt s'.mem ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840) 1008 = VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ ∧ s'.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840 ∧
        s'.gpr .rdi = 0 := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, VG.Proof.MlDsa.X86_64.Sample.sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ⟨h.env.keep hm1 (k1.mono (by decide)), ?_, hsi1, hdi1⟩
  rw [hm1, h.out]; exact (VG.Proof.MlDsa.Sample.G_eq _ _).symm

/-- The loop: `LAt σ 336` at the end. -/
theorem loop_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J6 168 1008 (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ s) : WP isa rnLoop s (VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ 336) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat0 h) fun s1 ⟨he, hout, hsi, hdi⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 336)
    (by xrun) (by decide)) fun s2 ⟨⟨hm, hcx⟩, hk⟩ => ?_)
  refine wp_countdown (N := 336) (by decide) (by decide) (VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ) (fun t ht s hI _ =>
    WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_step hp ht hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he.keep hm (hk.mono (by decide)), by rw [hm]; exact hout, by rw [hk.gpr (by decide), hsi]; simp,
      by rw [hk.gpr (by decide), hdi]; rfl, hcx, by rw [hm]; exact stored_nil _ _⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ 336 s) :
    WP isa (.block (retJ ++ VG.Impl.MlDsa.X86_64.Sample.epi)) s fun s' => rnK.post σ s' ∧ gprPreserved σ s' := by
  have hL : VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ 336 = rnFold [] (VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ) := by
    simp only [VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt]; rw [List.take_of_length_le (by rw [VG.Proof.MlDsa.X86_64.Sample.RejNtt.X_length])]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.retEpi_ok (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp) h.env h.rdi (VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt_length_le 336)) fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun hf => ?_⟩, hg⟩
  · rw [hax, hL]
  · rw [hm, ← hL]
    rw [← hL] at hf
    exact stored_polyIs h.stored hf

end

end RejNtt

theorem rejNTT_correct (σ : State) (hp : rnK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.rejNTT σ t s' ∧ abiPreserved σ s' ∧ rnK.post σ s' := by
  open RejNtt in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejNtt.pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.sponge_ok (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp) (rate := 168) (outlen := 1008) (.inr rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejNtt.loop_ok hp h2) fun s3 h3 => VG.Proof.MlDsa.X86_64.Sample.RejNtt.end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Ball`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_sample_in_ball`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(c̃, 272)` (`J6`), the zeroing of `c`, and the loop over the 264 bytes after
the sign bits, iteration `t` of which starts from `BAt σ t`: with the
polynomial and `i` that `bFold` computes from the first `t` of them, and the
sign bits not yet used in `r9` (`W σ`, the first 8 bytes as a `u64`, shifted
right once per coefficient set).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs IPoly n toRq ballParams)
open VG.Spec.Sha3 (bytesAt)

/-- `τ`, the `u32` argument in `edx`. -/
abbrev tauOf (s : State) : Nat := ((s.gpr .rdx).setWidth 32).toNat

/-- `vg_mldsa_sample_in_ball(ctilde = rdi, len = rsi, tau = edx, c = rcx, scratch = r8) -> eax`,
with 16 bytes of stack below `rsp`. -/
def sbK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .rcx), ⟨s.gpr .r8, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .rcx)) ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .r8, 2048⟩ ∧
    (pR (s.gpr .rcx)).Disjoint ⟨s.gpr .r8, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint ⟨s.gpr .r8, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rcx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r8, 2048⟩ ∧ (s.gpr .r8).toNat + 2048 ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat, VG.Proof.MlDsa.X86_64.Sample.tauOf s) ∈ ballParams
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (ballFold (VG.Proof.MlDsa.X86_64.Sample.tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 then 1 else 0) ∧
      ((ballFold (VG.Proof.MlDsa.X86_64.Sample.tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 →
        PolyIs s'.mem (s.gpr .rcx) (toRq (ballFold (VG.Proof.MlDsa.X86_64.Sample.tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).1))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat = bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat

theorem readW64_getLsbD (m : Mem) (a : Addr) {k : Nat} (hk : k < 64) :
    (m.readW a 64).getLsbD k = (m (a + BitVec.ofNat 64 (k / 8))).getLsbD (k % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (j := k / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, show k % 8 < 8 by omega, decide_true, Bool.true_and, hk]
  congr 1; omega

/-- The `u64` at `p`, from the bytes there. -/
theorem readW_leNat (m : Mem) (p : Addr) (L : List Byte) (h : ∀ k < 8, m (p + BitVec.ofNat 64 k) = L.getD k 0) :
    m.readW p 64 = BitVec.ofNat 64 (leNat (L.take 8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [VG.Proof.MlDsa.X86_64.Sample.readW64_getLsbD m p hk, h _ (by omega), BitVec.getLsbD_ofNat, testBit_leNat, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  simp [hk]

namespace Ball

theorem ballParams_le {len τ : Nat} (h : (len, τ) ∈ ballParams) : len ≤ 64 ∧ 39 ≤ τ ∧ τ ≤ 60 := by
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega

/-- The call. -/
abbrev spOf (σ : State) : VG.Proof.MlDsa.X86_64.Sample.Sp :=
  ⟨σ.gpr .rdi, (σ.gpr .rsi).toNat, σ.gpr .r8, σ.gpr .rcx, BitVec.setWidth 64 ((σ.gpr .rdx).setWidth 32)⟩

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) (σ.gpr .rsi).toNat

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (VG.Proof.MlDsa.X86_64.Sample.Ball.B σ) 272

/-- The first `i`. -/
abbrev i0 (σ : State) : Nat := 256 - VG.Proof.MlDsa.X86_64.Sample.tauOf σ

/-- The sign bits, as a `u64`. -/
abbrev W (σ : State) : BitVec 64 := BitVec.ofNat 64 (leNat ((VG.Proof.MlDsa.X86_64.Sample.Ball.X σ).take 8))

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (σ : State) (t : Nat) : IPoly × Nat :=
  bFold (VG.Proof.MlDsa.X86_64.Sample.tauOf σ) (signs (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ)) (Vector.replicate n 0, VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ) (((VG.Proof.MlDsa.X86_64.Sample.Ball.X σ).drop 8).take t)

section
variable {σ : State} (hp : sbK.pre σ)
include hp

theorem params : (σ.gpr .rsi).toNat ≤ 64 ∧ 39 ≤ VG.Proof.MlDsa.X86_64.Sample.tauOf σ ∧ VG.Proof.MlDsa.X86_64.Sample.tauOf σ ≤ 60 :=
  VG.Proof.MlDsa.X86_64.Sample.Ball.ballParams_le hp.2.2.2.2.2.2.2.2.2.2.2.2

theorem spOk : VG.Proof.MlDsa.X86_64.Sample.SpOk (VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (σ.gpr .rsi).toNat < 2 ^ 64; have := (VG.Proof.MlDsa.X86_64.Sample.Ball.params hp).1; omega⟩

theorem pro_ok : WP isa (.block (VG.Impl.MlDsa.X86_64.Sample.pro .r8 .rcx (.reg .rdx) (.reg .rsi))) σ (VG.Proof.MlDsa.X86_64.Sample.J0 (VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rcx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rdx).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = σ.gpr .rsi)
    (by unfold VG.Impl.MlDsa.X86_64.Sample.pro; xrun [VG.Proof.MlDsa.X86_64.Sample.inScrσ (VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp) (a := 2024) (n := 8) (by omega),
      VG.Proof.MlDsa.X86_64.Sample.inScrσ (VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp) (a := 2032) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Sample.inScrσ (VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp) (a := 2040) (n := 8) (by omega)])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ =>
      VG.Proof.MlDsa.X86_64.Sample.pro_J0 hm hbx hbp h12 hcx (by rw [h8]; simp) k

omit hp in
theorem X_length : (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ).length = 272 := VG.Proof.MlDsa.Sample.H_length _ _

/-! ## The zeroing, and the setup of the loop -/

/-- After the zeroing. -/
structure ZDone (σ s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.X86_64.Sample.Ball.X σ
  st : VG.Proof.MlDsa.X86_64.Sample.CStored s.mem (σ.gpr .rcx) (Vector.replicate n 0)

theorem zero_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.J6 136 272 (VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ) σ s) : WP isa bZero s (VG.Proof.MlDsa.X86_64.Sample.Ball.ZDone σ) := by
  have hp' := VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.bZero_ok s h.env.rbp (by rw [h.env.wr, hp.2.1]; simp)) fun s' ⟨k, hf, hst⟩ => ?_
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' k) 64 = s.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (VG.Proof.MlDsa.X86_64.Sample.a_scr' hp' h2).symm) (by decide)
  have k' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := k.mono (by simp)
  refine ⟨⟨k'.2.1.trans h.env.rd, k'.2.2.trans h.env.wr, by rw [k'.gpr (by decide), h.env.rbx],
    by rw [k'.gpr (by decide), h.env.rbp], by rw [k'.gpr (by decide), h.env.r12],
    by rw [k'.gpr (by decide), h.env.rsp], fun r hr => by rw [k'.gpr (VG.Proof.MlDsa.X86_64.Sample.r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩, ?_, hst⟩
  rw [MlKem.bytesAt_frame hf (by simpa using (VG.Proof.MlDsa.X86_64.Sample.a_scr' hp' (a := 840) (n := 272) (by omega)).symm) (by omega), h.out]
  exact (VG.Proof.MlDsa.Sample.H_eq _ _).symm

/-- At the start of iteration `t`. -/
structure BAt (σ : State) (t : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.X86_64.Sample.Ball.X σ
  rsi : s.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 848 + BitVec.ofNat 64 t
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2
  r9 : s.gpr .r9 = VG.Proof.MlDsa.X86_64.Sample.Ball.W σ >>> ((VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2 - VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (264 - t)
  st : VG.Proof.MlDsa.X86_64.Sample.CStored s.mem (σ.gpr .rcx) (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).1

omit hp in
theorem out_getD {s : State} (hout : bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.X86_64.Sample.Ball.X σ) {j : Nat} (hj : j < 272) :
    s.mem ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 840 + BitVec.ofNat 64 j) = (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ).getD j 0 := by
  have := congrArg (fun L => L.getD j 0) hout
  rw [MlKem.bytesAt_getD _ _ hj] at this
  exact this

theorem setup_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.Ball.ZDone σ s) :
    WP isa (.block bSetup) s fun s1 => WP isa (.block [.mov32 .rcx (.imm 264)]) s1 (VG.Proof.MlDsa.X86_64.Sample.Ball.BAt σ 0) := by
  have hp' := VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp
  have ht := (VG.Proof.MlDsa.X86_64.Sample.Ball.params hp).2
  refine (WP.mono (WP.keep [.r9, .rdi, .rsi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r9 = s.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 840) 64 ∧ s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ) ∧
      s'.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' 848) (by
        unfold bSetup
        xrun [h.env.rbx, h.env.r12, VG.Proof.MlDsa.X86_64.Sample.inScrRd hp' h.env (a := 840) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Sample.sx840, VG.Proof.MlDsa.X86_64.Sample.sw32_64,
          show BitVec.signExtend 64 (848 : BitVec 32) = BitVec.ofNat 64 848 by decide]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, show (256 : BitVec 32).toNat = 256 from rfl]
        have := ((σ.gpr .rdx).setWidth 32).isLt
        simp only [VG.Proof.MlDsa.X86_64.Sample.Ball.i0, VG.Proof.MlDsa.X86_64.Sample.tauOf] at ht ⊢
        omega) (by decide)) fun s1 ⟨⟨hm1, h91, hdi1, hsi1⟩, k1⟩ => ?_)
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 264)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  have he1 := h.env.keep hm1 (k1.mono (by decide))
  have hSt : VG.Proof.MlDsa.X86_64.Sample.Ball.St σ 0 = (Vector.replicate n 0, VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ) := rfl
  refine ⟨he1.keep hm2 (k2.mono (by decide)), by rw [hm2, hm1]; exact h.out,
    by rw [k2.gpr (by decide), hsi1]; simp, by rw [k2.gpr (by decide), hdi1, hSt], ?_, hcx,
    by rw [hm2, hm1, hSt]; exact h.st⟩
  rw [k2.gpr (by decide), h91, hSt, Nat.sub_self, BitVec.ushiftRight_zero]
  exact VG.Proof.MlDsa.X86_64.Sample.readW_leNat _ _ _ fun k hk => VG.Proof.MlDsa.X86_64.Sample.Ball.out_getD h.out (by omega)

/-! ## The loop -/

omit hp in
theorem St_le (t : Nat) : (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2 ≤ 256 := bFold_le (by simp) _

omit hp in
theorem St_ge (t : Nat) : VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ ≤ (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2 :=
  bFold_ge (τ := VG.Proof.MlDsa.X86_64.Sample.tauOf σ) (h := signs (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ)) (Vector.replicate n 0, VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ) _

omit hp in
theorem take_succ'' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The sign bit of `i`. -/
theorem sign_bit {i : Nat} (hi0 : VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ ≤ i) (hi : i < 256) :
    (VG.Proof.MlDsa.X86_64.Sample.Ball.W σ >>> (i - VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ)).getLsbD 0 = (signs (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ)).getD (i + VG.Proof.MlDsa.X86_64.Sample.tauOf σ - 256) false := by
  have ht := (VG.Proof.MlDsa.X86_64.Sample.Ball.params hp).2
  simp only [VG.Proof.MlDsa.X86_64.Sample.Ball.i0] at hi0
  rw [BitVec.getLsbD_ushiftRight, Nat.add_zero, signs_getD, BitVec.getLsbD_ofNat,
    show i - (256 - VG.Proof.MlDsa.X86_64.Sample.tauOf σ) = i + VG.Proof.MlDsa.X86_64.Sample.tauOf σ - 256 by omega,
    decide_eq_true (show i + VG.Proof.MlDsa.X86_64.Sample.tauOf σ - 256 < 64 by omega), Bool.true_and]

/-- An iteration, from `BAt`. -/
theorem bat_step {t : Nat} {s : State} (ht : t < 264) (h : VG.Proof.MlDsa.X86_64.Sample.Ball.BAt σ t s) :
    WP isa bBody s fun s' => VG.Proof.MlDsa.X86_64.Sample.Ball.BAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (264 - t) - 1 == 0) := by
  have hp' := VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp
  have hw : pR (σ.gpr .rcx) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  have hle := VG.Proof.MlDsa.X86_64.Sample.Ball.St_le (σ := σ) t
  have hge := VG.Proof.MlDsa.X86_64.Sample.Ball.St_ge (σ := σ) t
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.bBody_ok s (τ := VG.Proof.MlDsa.X86_64.Sample.tauOf σ) (h := signs (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ)) (c := (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).1) (aP := σ.gpr .rcx) h.env.rbp h.rdi
    hle hw (List.mem_append_right _ hw) h.st
    (by rw [h.rsi, VG.Proof.MlDsa.X86_64.Sample.at_add]; exact VG.Proof.MlDsa.X86_64.Sample.inScrRd hp' h.env (by omega))
    (fun hi => by rw [h.r9]; exact VG.Proof.MlDsa.X86_64.Sample.Ball.sign_bit hp hge hi)) fun s' ⟨hdi, hst, hf, h9, hsi, hcx, hz, hk⟩ => ?_
  have hb : s.mem (s.gpr .rsi) = ((VG.Proof.MlDsa.X86_64.Sample.Ball.X σ).drop 8).getD t 0 := by
    rw [h.rsi, VG.Proof.MlDsa.X86_64.Sample.at_add, show 848 + t = 840 + (8 + t) by omega, ← VG.Proof.MlDsa.X86_64.Sample.at_add, VG.Proof.MlDsa.X86_64.Sample.Ball.out_getD h.out (by omega),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have ht1 : VG.Proof.MlDsa.X86_64.Sample.Ball.St σ (t + 1) = bStep (VG.Proof.MlDsa.X86_64.Sample.tauOf σ) (signs (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ)) (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t) (((VG.Proof.MlDsa.X86_64.Sample.Ball.X σ).drop 8).getD t 0) := by
    simp only [VG.Proof.MlDsa.X86_64.Sample.Ball.St]
    rw [VG.Proof.MlDsa.X86_64.Sample.Ball.take_succ'' _ (by rw [List.length_drop, VG.Proof.MlDsa.X86_64.Sample.Ball.X_length]; omega), bFold_snoc]
  rw [hb, ← ht1] at hdi hst h9
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' k) 64 = s.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.Ball.spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (VG.Proof.MlDsa.X86_64.Sample.a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp], fun r hr => by rw [hk'.gpr (VG.Proof.MlDsa.X86_64.Sample.r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (VG.Proof.MlDsa.X86_64.Sample.a_scr' hp' (a := 840) (n := 272) (by omega)).symm)
      (by omega)]; exact h.out, by rw [hsi, h.rsi, VG.Proof.MlDsa.X86_64.Sample.offAdd], hdi, ?_,
    by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩
  rw [h9, h.r9]
  have hs : (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ (t + 1)).2 = (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2 ∨ (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ (t + 1)).2 = (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2 + 1 := by
    rw [ht1]; unfold bStep; split
    · split
      · exact .inl rfl
      · exact .inr rfl
    · exact .inl rfl
  rcases hs with e | e
  · rw [ifT e, e]
  · rw [ifF (by omega), e, ← BitVec.shiftRight_add, show (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2 + 1 - VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ = (VG.Proof.MlDsa.X86_64.Sample.Ball.St σ t).2 - VG.Proof.MlDsa.X86_64.Sample.Ball.i0 σ + 1 by omega]

theorem loop_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.Ball.ZDone σ s) : WP isa bLoop s (VG.Proof.MlDsa.X86_64.Sample.Ball.BAt σ 264) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.Ball.setup_ok hp h) fun _ h1 => WP.seq (WP.mono h1 fun _ h2 =>
    wp_countdown (N := 264) (by decide) (by decide) (VG.Proof.MlDsa.X86_64.Sample.Ball.BAt σ) (fun t ht s hI _ => WP.mono (VG.Proof.MlDsa.X86_64.Sample.Ball.bat_step hp ht hI)
      fun s' ⟨hI', hz⟩ => ⟨hI', by rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
        by rw [hz, hI.rcx]⟩) (fun _ h => h) h2 h2.rcx))

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.Ball.BAt σ 264 s) :
    WP isa (.block (retJ ++ VG.Impl.MlDsa.X86_64.Sample.epi)) s fun s' => sbK.post σ s' ∧ gprPreserved σ s' := by
  have hL : VG.Proof.MlDsa.X86_64.Sample.Ball.St σ 264 = ballFold (VG.Proof.MlDsa.X86_64.Sample.tauOf σ) (VG.Proof.MlDsa.X86_64.Sample.Ball.X σ) := by
    simp only [VG.Proof.MlDsa.X86_64.Sample.Ball.St, ballFold, VG.Proof.MlDsa.X86_64.Sample.Ball.i0]; rw [List.take_of_length_le (by rw [List.length_drop, VG.Proof.MlDsa.X86_64.Sample.Ball.X_length])]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.retEpi_ok (VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp) h.env h.rdi (VG.Proof.MlDsa.X86_64.Sample.Ball.St_le 264)) fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun hf => ?_⟩, hg⟩
  · rw [hax, hL]
  · rw [hm]
    have hst := h.st
    rw [hL] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map]

end

end Ball

theorem sampleInBall_correct (σ : State) (hp : sbK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.sampleInBall σ t s' ∧ abiPreserved σ s' ∧ sbK.post σ s' := by
  open Ball in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.Ball.pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.sponge_ok (VG.Proof.MlDsa.X86_64.Sample.Ball.spOk hp) (rate := 136) (outlen := 272) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.Ball.zero_ok hp h2) fun s3 h3 => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.Ball.loop_ok hp h3) fun s4 h4 => VG.Proof.MlDsa.X86_64.Sample.Ball.end_ok hp h4))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, squeezing

`vg_mldsa_rej_ntt_poly4_avx2` absorbs the seeds and squeezes three blocks of
each as `vg_mlkem_sample_ntt4_avx2` does (`Proof/MlKem/X86_64/S4*.lean`, whose
precondition, layout and invariants it shares), then three more to the same
buffers. `SqT σ t n` is `SqInv σ n` (`S4Squeeze.lean`) after `t` blocks
squeezed before: the states are permuted `t + n` times, and the buffers hold
bytes `168 t` to `168 (t + n)` of each seed's output. A squeeze writes only
below the saved registers (`sqT_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64 (Keep ea_at)
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.MlKem (seed4 poly4)
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (xofByte)
open VG.Proof.Sha3.X86_64.X4 (la Lanes4 byte_of_lanes4 permute4_ok)

/-- After `n` squeezes, `t` blocks after the absorption. -/
structure SqT (σ : State) (t n : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.S4.Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) fun k => iterF (t + n) (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k))
  buf : ∀ k < 4, ∀ p < 168 * n, s.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) (168 * t + p)

theorem sqT_of {σ s : State} (h : SqInv σ 0 s) : VG.Proof.MlDsa.X86_64.Rej4.SqT σ 0 0 s :=
  ⟨h.env, h.r14, h.rc, h.lanes, fun _ _ p hp => absurd hp (by omega)⟩

/-- The low part of the scratch space, which the squeezes write. -/
abbrev lowR (σ : State) : Region := ⟨scr σ, oSave⟩

/-- The permutation, after `n` squeezes. -/
theorem permT_ok {σ : State} (hp : Pre σ) {t n : Nat} (hn : n < 3) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.SqT σ t n s)
    {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', VG.Proof.MlKem.X86_64.S4.Env σ s' ∧ s'.gpr .r14 = 1 ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (scr σ) (fun k => iterF (t + n + 1) (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k))) ∧
      (∀ k < 4, ∀ p < 168 * n, s'.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) (168 * t + p)) ∧
      Frame [VG.Proof.MlDsa.X86_64.Rej4.lowR σ] s.mem s'.mem → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq Impl.Sha3.X86_64.X4.permute4 rest)) s Q := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (A := fun k => iterF (t + n) (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k)))
    (VG.Proof.MlKem.X86_64.S4.pre4 hp hrd hwr (by rw [hm]; exact h.rc)) hdi hsi hdx (by rw [hcx, VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.at', Offset.add_add])
    (by rw [hm]; exact h.lanes)) fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨scr σ, 800⟩ : Region), ⟨VG.Proof.MlKem.X86_64.S4.at' σ 800, 800⟩], Region.Sub r ⟨scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega)
    · exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨Env.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide), h.r14], fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_,
    by rw [← hm]; exact hf.sub fun r hr => ⟨VG.Proof.MlDsa.X86_64.Rej4.lowR σ, List.mem_singleton_self _, hsub r hr⟩⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega),
          Offset.disjoint (scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega) (by omega)
            (by omega)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · intro i hi k hk
    rw [hl i hi k hk]
    rfl
  · rw [buf_frame (by simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := oBuf) (n := 2016)
        (by simp only [oBuf]; omega) (by simp only [oBuf]; omega), Offset.disjoint (scr σ) (d := oBuf) (n := 2016)
          (e := 800) (k := 800) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)⟩) hf hk (by omega), hm]
    exact h.buf k hk p hp'

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXT (σ : State) (m₀ : Mem) (t n K I : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.S4.Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) (fun k => iterF (t + n + 1) (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k)))
  buf : ∀ k < 4, ∀ p < 504, (p < 168 * n ∨ (168 * n ≤ p ∧ p < 168 * n + 168 ∧ (k < K ∨ (k = K ∧ p < 168 * n + 8 * I)))) →
    s.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) (168 * t + p)
  fr : Frame [VG.Proof.MlDsa.X86_64.Rej4.lowR σ] m₀ s.mem

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem extT_step {σ : State} (hp : Pre σ) {m₀ : Mem} {t n K I : Nat} (hn : n < 3) (hK : K < 4) (hI : I < 21)
    {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.EXT σ m₀ t n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbx (oBuf + 504 * K + 168 * n + 8 * I)) .rax]) s (VG.Proof.MlDsa.X86_64.Rej4.EXT σ m₀ t n K (I + 1)) := by
  refine wp_movm (a := VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (in_scr' hp h.env.rd h.env.wr (by omega)) fun s₁ u₁ => wp_store (a := VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 168 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx]) (by rw [u₁.wr]; exact in_scr hp h.env.wr (by simp only [oBuf]; omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 168 * n + 8 * I)) (s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hsub : Region.Sub ⟨VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩ (VG.Proof.MlDsa.X86_64.Rej4.lowR σ) :=
    Offset.sub_base _ (by simp only [oBuf, oSave]; omega)
  have hf : Frame [⟨VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨Env.low h.env (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub) hf
      (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_,
    h.fr.trans (hf.sub fun r hr => ⟨VG.Proof.MlDsa.X86_64.Rej4.lowR σ, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩)⟩
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 168 * n + 8 * I ≤ p ∧ p < 168 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega) (by simp only [oBuf]; omega) (by decide),
        show 8 * (oBuf + 504 * k + p - (oBuf + 504 * k + 168 * n + 8 * I)) = 8 * (p - 168 * n - 8 * I) by omega,
        byte_readW _ _ (by omega), VG.Proof.MlKem.X86_64.S4.at', Offset.add_add,
        show 32 * I + 8 * k + (p - 168 * n - 8 * I) = 32 * ((8 * I + (p - 168 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 168 * n - 8 * I)) % 8 by omega,
        byte_of_lanes4 h.lanes hk (by omega), show t + n + 1 = (t + n) + 1 from rfl,
        ← VG.Proof.Sha3.Seed34.xofByte_A0 (B_length σ k) (by omega),
        show 168 * (t + n) + (8 * I + (p - 168 * n - 8 * I)) = 168 * t + p by omega]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega)]
      exact h.buf k hk p hp' (by omega)

/-- Block `n` of each state's output. -/
theorem extractT_ok {σ : State} (hp : Pre σ) {m₀ : Mem} {t n : Nat} (hn : n < 3) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Rej4.EXT σ m₀ t n 0 0 s) :
    WP isa (.block (VG.Impl.MlKem.X86_64.Sample4.extract n)) s fun s' => VG.Proof.MlDsa.X86_64.Rej4.SqT σ t (n + 1) s' ∧ Frame [VG.Proof.MlDsa.X86_64.Rej4.lowR σ] m₀ s'.mem := by
  rw [VG.Proof.MlKem.X86_64.S4.extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlDsa.X86_64.Rej4.EXT σ m₀ t n K 0 s) (fun K s hK h => ?_) 4 (Nat.le_refl _)
    s h) fun s' h' => ⟨⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega) (by omega)⟩, h'.fr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => VG.Proof.MlDsa.X86_64.Rej4.EXT σ m₀ t n K I s) (fun I s hI h => VG.Proof.MlDsa.X86_64.Rej4.extT_step hp hn hK hI h)
    21 (Nat.le_refl _) s h) fun s' h' =>
      ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega), h'.fr⟩

/-- `squeeze4 n`: after `n + 1` squeezes; it writes only below the saved
registers. -/
theorem sqT_ok {σ : State} (hp : Pre σ) {t n : Nat} (hn : n < 3) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.SqT σ t n s) :
    WP isa (squeeze4 n) s fun s' => VG.Proof.MlDsa.X86_64.Rej4.SqT σ t (n + 1) s' ∧ Frame [VG.Proof.MlDsa.X86_64.Rej4.lowR σ] s.mem s'.mem := by
  unfold squeeze4
  exact VG.Proof.MlDsa.X86_64.Rej4.permT_ok hp hn h fun s' ⟨he, h14, hrc, hl, hb, hf⟩ =>
    VG.Proof.MlDsa.X86_64.Rej4.extractT_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega), hf⟩

end VG.Proof.MlDsa.X86_64.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Parse`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, sampling

Each half of a seed's sampling (`half`) runs 168 iterations of
`vg_mldsa_rej_ntt_poly`'s loop (`rnBody_ok`) on the 504 bytes of the seed's
buffer, which hold bytes `504 h` to `504 h + 503` of its output `Xb` (`G` of
the seed, as `vg_mldsa_rej_ntt_poly` squeezes it: `Xb_getD`): from `j`
coefficients sampled, it samples those of the first `504 (h + 1)` bytes
(`half_ok`), and writes only the seed's polynomial.
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half)
open VG.Proof.MlKem.X86_64 (Keep ea_at wp_countdown add_ofNat_zero pR WP.keep ofNat64_pred)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold rnStep rnFold_snoc rnFold_length_le Stored stored_nil stored_frame G_eq G_length)
open VG.Proof.MlDsa.X86_64.Sample (rnBody_ok CoeffsWr)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlKem (xofByte xof_squeezeFrom_getElem)

/-- ML-KEM's `S4.Env`, which this function shares. -/
abbrev EnvK := VG.Proof.MlKem.X86_64.S4.Env

/-- The 1008 bytes of output of seed `k`, which `vg_mldsa_rej_ntt_poly` samples from. -/
abbrev Xb (σ : State) (k : Nat) : List Byte := Spec.MlDsa.G (VG.Proof.MlKem.X86_64.S4.B σ k) 1008

theorem Xb_getD (σ : State) (k : Nat) {p : Nat} (hp : p < 1008) : (VG.Proof.MlDsa.X86_64.Rej4.Xb σ k).getD p 0 = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) p := by
  have e := xof_squeezeFrom_getElem (VG.Proof.MlKem.X86_64.S4.B σ k) (pos := 0) (d := 1008) hp
  rw [Nat.zero_add] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [VG.Proof.MlDsa.X86_64.Rej4.Xb, VG.Proof.MlDsa.Sample.G_length]; exact hp), Option.getD_some, ← e]
  simp only [VG.Proof.MlDsa.X86_64.Rej4.Xb, VG.Proof.MlDsa.Sample.G_eq]

/-- The coefficients of seed `k` after `n` iterations. -/
abbrev Lt (σ : State) (k n : Nat) : List Zq := rnFold [] ((VG.Proof.MlDsa.X86_64.Rej4.Xb σ k).take (3 * n))

theorem Lt_length_le (σ : State) (k n : Nat) : (VG.Proof.MlDsa.X86_64.Rej4.Lt σ k n).length ≤ 256 := rnFold_length_le (by simp) _

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A byte the frame's regions are apart from is unchanged. -/
theorem frame_byte {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    {x : Addr} (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
/-- Polynomial `K` lies in `a`. -/
theorem sub_poly {K : Nat} (hK : K < 4) : Region.Sub (pR (poly4 (aP σ) K)) (aR σ) := Offset.sub_base _ (by omega)

/-- A part of the scratch space is apart from polynomial `K`. -/
theorem scr_poly {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ 8192) :
    ∀ r ∈ [pR (poly4 (aP σ) K)], Region.Disjoint ⟨VG.Proof.MlKem.X86_64.S4.at' σ a, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Region.Disjoint.sub_right (Region.Disjoint.sub_left hp.a_scr.symm (VG.Proof.MlKem.X86_64.S4.sub_scr h)) (VG.Proof.MlDsa.X86_64.Rej4.sub_poly hK)

omit hp in
/-- Two polynomials are apart. -/
theorem poly_poly {K k : Nat} (hK : K < 4) (hk : k < 4) (hne : k ≠ K) :
    ∀ r ∈ [pR (poly4 (aP σ) K)], (VG.Proof.MlDsa.Sample.polyR (poly4 (aP σ) k)).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
    (by omega)

/-- Writes to polynomial `K` keep `Env`. -/
theorem env_poly {K : Nat} (hK : K < 4) {s s' : State} (he : VG.Proof.MlDsa.X86_64.Rej4.EnvK σ s)
    (hf : Frame [pR (poly4 (aP σ) K)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : VG.Proof.MlDsa.X86_64.Rej4.EnvK σ s' := by
  have hsub := VG.Proof.MlDsa.X86_64.Rej4.sub_poly (σ := σ) hK
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, he.frame.trans (hf.sub fun r hr => ?_)⟩
  · rw [hf.readW (Region.contains_self _ _) (VG.Proof.MlDsa.X86_64.Rej4.scr_poly hp hK (by simp only [oSave]; omega)) (by decide)]
    exact he.saved i hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨aR σ, by simp, hsub⟩

/-- Each coefficient of polynomial `K` is writable. -/
theorem coeffsWr {K : Nat} (hK : K < 4) {s : State} (he : VG.Proof.MlDsa.X86_64.Rej4.EnvK σ s) : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr (poly4 (aP σ) K) := by
  intro j hj
  rw [he.wr, hp.wr]
  refine ⟨aR σ, by simp, ?_⟩
  rw [VG.Proof.MlDsa.Sample.coeffAddr, poly4, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

end

/-! ## A half -/

/-- At iteration `t` of half `h` of seed `K`, from `s₀`. -/
structure HAt (σ s₀ : State) (K h t : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Rej4.EnvK σ s
  rsi : s.gpr .rsi = VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.Lt σ K (168 * h + t)).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (168 - t)
  rbp : s.gpr .rbp = poly4 (aP σ) K
  out : ∀ p < 504, s.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ K) (504 * h + p)
  stored : Stored s.mem (poly4 (aP σ) K) (VG.Proof.MlDsa.X86_64.Rej4.Lt σ K (168 * h + t))
  fr : Frame [pR (poly4 (aP σ) K)] s₀.mem s.mem
  kp : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp] s₀ s

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem hat_byte {s₀ : State} {K h t : Nat} (hh : h < 2) {s : State} (hI : VG.Proof.MlDsa.X86_64.Rej4.HAt σ s₀ K h t s) {j : Nat}
    (hj : 3 * t + j < 504) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 j) = (VG.Proof.MlDsa.X86_64.Rej4.Xb σ K).getD (3 * (168 * h + t) + j) 0 := by
  have e := hI.out (3 * t + j) hj
  rw [VG.Proof.MlKem.X86_64.S4.at'] at e
  rw [hI.rsi, VG.Proof.MlKem.X86_64.S4.at', Offset.add_add, Offset.add_add, e, VG.Proof.MlDsa.X86_64.Rej4.Xb_getD σ K (by omega)]
  congr 1; omega

theorem hat_regions {s₀ : State} {K h t : Nat} (hK : K < 4) {s : State} (hI : VG.Proof.MlDsa.X86_64.Rej4.HAt σ s₀ K h t s) {j : Nat}
    (hj : 3 * t + j < 504) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [hI.rsi, VG.Proof.MlKem.X86_64.S4.at', Offset.add_add, Offset.add_add]
  exact in_scr' hp hI.env.rd hI.env.wr (by simp only [oBuf]; omega)

/-- An iteration. -/
theorem hat_step {s₀ : State} {K h t : Nat} (hK : K < 4) (hh : h < 2) (ht : t < 168) {s : State}
    (hI : VG.Proof.MlDsa.X86_64.Rej4.HAt σ s₀ K h t s) :
    WP isa rnBody s fun s' => VG.Proof.MlDsa.X86_64.Rej4.HAt σ s₀ K h (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (168 - t) - 1 == 0) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.rnBody_ok s (aP := poly4 (aP σ) K) hI.rbp hI.rdi (VG.Proof.MlDsa.X86_64.Rej4.Lt_length_le σ K _) (VG.Proof.MlDsa.X86_64.Rej4.coeffsWr hp hK hI.env)
    hI.stored (by simpa using VG.Proof.MlDsa.X86_64.Rej4.hat_regions hp hK hI (j := 0) (by omega)) (VG.Proof.MlDsa.X86_64.Rej4.hat_regions hp hK hI (by omega))
    (VG.Proof.MlDsa.X86_64.Rej4.hat_regions hp hK hI (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := VG.Proof.MlDsa.X86_64.Rej4.hat_byte hh hI (j := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  have ht3 : VG.Proof.MlDsa.X86_64.Rej4.Lt σ K (168 * h + (t + 1)) = rnStep (VG.Proof.MlDsa.X86_64.Rej4.Lt σ K (168 * h + t)) ((VG.Proof.MlDsa.X86_64.Rej4.Xb σ K).getD (3 * (168 * h + t)) 0)
      ((VG.Proof.MlDsa.X86_64.Rej4.Xb σ K).getD (3 * (168 * h + t) + 1) 0) ((VG.Proof.MlDsa.X86_64.Rej4.Xb σ K).getD (3 * (168 * h + t) + 2) 0) := by
    simp only [VG.Proof.MlDsa.X86_64.Rej4.Lt]
    rw [show 3 * (168 * h + (t + 1)) = 3 * (168 * h + t) + 3 by omega,
      VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [VG.Proof.MlDsa.X86_64.Rej4.Xb, VG.Proof.MlDsa.Sample.G_length]; omega),
      rnFold_snoc _ (by rw [List.length_take, VG.Proof.MlDsa.X86_64.Rej4.Xb, VG.Proof.MlDsa.Sample.G_length]; omega)]
  rw [e0, VG.Proof.MlDsa.X86_64.Rej4.hat_byte hh hI (j := 1) (by omega), VG.Proof.MlDsa.X86_64.Rej4.hat_byte hh hI (j := 2) (by omega), ← ht3] at hdi hst
  have hk' : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := hk
  refine ⟨⟨VG.Proof.MlDsa.X86_64.Rej4.env_poly hp hK hI.env hf hk'.2.1 hk'.2.2 fun r hr => hk'.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, hI.rsi, Offset.add_add, show 3 * t + 3 = 3 * (t + 1) by omega], hdi,
    by rw [hcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
    by rw [hk'.gpr (by decide), hI.rbp],
    fun p hp' => by
      rw [VG.Proof.MlDsa.X86_64.Rej4.frame_byte hf (VG.Proof.MlDsa.X86_64.Rej4.scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega))
        (Region.contains_self _ _)]
      exact hI.out p hp',
    hst, hI.fr.trans hf, (hI.kp.trans hk').mono (by simp)⟩, by rw [hz, hI.rcx]⟩

/-- Before a half: what holds of seed `K`. -/
structure HPre (σ : State) (K h : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Rej4.EnvK σ s
  out : ∀ p < 504, s.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ K) (504 * h + p)
  j : s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oJ + 8 * K)) 64 = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.Lt σ K (168 * h)).length
  stored : Stored s.mem (poly4 (aP σ) K) (VG.Proof.MlDsa.X86_64.Rej4.Lt σ K (168 * h))

omit hp in
theorem sxB {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (oBuf + 504 * K)) =
    BitVec.ofNat 64 (oBuf + 504 * K) := VG.Proof.MlDsa.X86_64.Rej4.sx_ofNat (by simp only [oBuf]; omega)

omit hp in
theorem sxP {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (1024 * K)) =
    BitVec.ofNat 64 (1024 * K) := VG.Proof.MlDsa.X86_64.Rej4.sx_ofNat (by omega)

/-- The setup of a half: at iteration 0, from `j` kept. -/
theorem hsetup_ok {K h : Nat} (hK : K < 4) {s : State} (hI : VG.Proof.MlDsa.X86_64.Rej4.HPre σ K h s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
      .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
      .mov .rdi (.mem (at_ .rbx (oJ + 8 * K))), .mov32 .rcx (.imm 168)]) s (VG.Proof.MlDsa.X86_64.Rej4.HAt σ s K h 0) := by
  have hin : InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 :=
    in_scr' hp hI.env.rd hI.env.wr (by simp only [oJ]; omega)
  refine WP.mono (WP.keep [.rsi, .rbp, .rdi, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K) ∧ s'.gpr .rbp = poly4 (aP σ) K ∧
      s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.Lt σ K (168 * h)).length ∧ s'.gpr .rcx = BitVec.ofNat 64 168)
    (by
      xrun [hI.env.rbx, hI.env.r13, VG.Proof.MlDsa.X86_64.Rej4.sxB hK, VG.Proof.MlDsa.X86_64.Rej4.sxP hK, hin, hI.j]
      rfl)
    rfl) fun s₁ ⟨⟨hm, hsi, hbp, hdi, hcx⟩, k₁⟩ => ?_
  exact ⟨hI.env.keep hm k₁ (by decide), by rw [hsi, add_ofNat_zero],
    by rw [hdi, Nat.add_zero], by rw [hcx], hbp, by rw [hm]; exact hI.out, by rw [hm, Nat.add_zero]; exact hI.stored,
    by rw [hm]; exact Frame.refl _ _, k₁.mono (by simp)⟩

/-- The loop of a half, from iteration 0. -/
theorem hloop_ok {s₀ : State} {K h : Nat} (hK : K < 4) (hh : h < 2) {s : State} (hI : VG.Proof.MlDsa.X86_64.Rej4.HAt σ s₀ K h 0 s) :
    WP isa (.loop rnBody .ne) s (VG.Proof.MlDsa.X86_64.Rej4.HAt σ s₀ K h 168) := by
  refine wp_countdown (N := 168) (by decide) (by decide) (fun t u => VG.Proof.MlDsa.X86_64.Rej4.HAt σ s₀ K h t u)
    (fun t ht u hu _ => WP.mono (VG.Proof.MlDsa.X86_64.Rej4.hat_step hp hK hh ht hu) fun u' ⟨hu', hz⟩ => ⟨hu', ?_, by rw [hz, hu.rcx]⟩)
    (fun _ h => h) hI hI.rcx
  rw [hu'.rcx, hu.rcx, ofNat64_pred (by omega) (by omega)]; rfl

/-- A half of seed `K`: the coefficients of the first `504 (h + 1)` bytes,
writing only polynomial `K`. -/
theorem half_ok {K h : Nat} (hK : K < 4) (hh : h < 2) {s : State} (hI : VG.Proof.MlDsa.X86_64.Rej4.HPre σ K h s) :
    WP isa (half K) s (VG.Proof.MlDsa.X86_64.Rej4.HAt σ s K h 168) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.hsetup_ok hp hK hI) fun _ h₁ => VG.Proof.MlDsa.X86_64.Rej4.hloop_ok hp hK hh h₁)

end

end VG.Proof.MlDsa.X86_64.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly`, constant time but for the seed

Two runs whose seeds (the declared leak) and pointers agree leak the same: the
prologue and the blocks around the loop by the taint analysis, the sponge by
`sponge_ct`, and the loop, whose branches and stores depend on the XOF output,
by relating the two runs iteration by iteration (`body_ct`): both are at the
same iteration with the same coefficients sampled and the same bytes to read,
so each branch goes the same way and each store goes to the same address.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Spec.Sha3 (bytesAt)

/-- What holds of every run of `c` from `s` that `Q a` does, for any `a`
with `Pre a` (by determinism). -/
theorem WP.all' {c : Prog isa} {s : State} {α : Sort _} {Pre : α → Prop} {Q : α → State → Prop}
    (h : ∀ a, Pre a → WP isa c s (Q a)) (hne : ∃ a, Pre a) : WP isa c s fun s' => ∀ a, Pre a → Q a s' := by
  obtain ⟨a₀, h₀⟩ := hne
  obtain ⟨t, s', e, -⟩ := h a₀ h₀
  refine ⟨t, s', e, fun a ha => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h a ha
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

theorem nil_regs {P : State → State → Prop} : ∀ x y, P x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

namespace RejNttCT

/-! ## A try -/

theorem rnTry_all (s : State) (hne : ∃ aP L, VG.Proof.MlDsa.X86_64.Sample.TryPre s aP L) :
    WP isa rnTry s fun s' => ∀ aP L, VG.Proof.MlDsa.X86_64.Sample.TryPre s aP L →
      s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.rnTryL L ((s.gpr .r8).setWidth 32).toNat).length ∧
      VG.Proof.MlDsa.Sample.Stored s'.mem aP (VG.Proof.MlDsa.X86_64.Sample.rnTryL L ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] s.mem s'.mem ∧
      Keep [.rdi] s s' := by
  have := WP.all' (Pre := fun p : Addr × List Zq => VG.Proof.MlDsa.X86_64.Sample.TryPre s p.1 p.2)
    (Q := fun p s' => s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.rnTryL p.2 ((s.gpr .r8).setWidth 32).toNat).length ∧
      VG.Proof.MlDsa.Sample.Stored s'.mem p.1 (VG.Proof.MlDsa.X86_64.Sample.rnTryL p.2 ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR p.1] s.mem s'.mem ∧
      Keep [.rdi] s s')
    (fun p h => VG.Proof.MlDsa.X86_64.Sample.rnTry_ok s h) (by obtain ⟨aP, L, h⟩ := hne; exact ⟨(aP, L), h⟩)
  exact WP.mono this fun s' h aP L hp => h (aP, L) hp

/-- The hypotheses of `rnMid_ok`. -/
structure MPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP
  st : VG.Proof.MlDsa.Sample.Stored s.mem aP L
  cf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))

/-- After the loads. -/
def R1 (s₁ s₂ : State) : Prop :=
  ∃ aP L, VG.Proof.MlDsa.X86_64.Sample.RejNttCT.MPre s₁ aP L ∧ VG.Proof.MlDsa.X86_64.Sample.RejNttCT.MPre s₂ aP L ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsi = s₂.gpr .rsi

theorem traceTry {h1 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .r8 (.imm qImm)]) h1).isSome = true)
    {h2 : VG.Taint.Hint X86_64.Taint.T}
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi]) (.block [.store32 aJ .r8, .alu .add .rdi (.imm 1)])
      h2).isSome = true)
    {h3 : VG.Taint.Hint X86_64.Taint.T} (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true) :
    RelCT isa (fun s₁ s₂ => s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
      (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32) rnTry fun _ _ => True := by
  refine RelCT.seq (R := fun (s₁ s₂ : State) => s₁.cf = s₂.cf ∧ s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi)
    (RelCT.postDep (F := fun (x x' : State) => x'.cf = some (decide (((x.gpr .r8).setWidth 32).toNat < q)) ∧
        x'.gpr = x.gpr)
      (taintRel [] VG.Proof.MlDsa.X86_64.Sample.nil_regs c1)
      (fun x y _ => ⟨WP.mono (VG.Proof.MlDsa.X86_64.Sample.rnCmp_ok x) fun _ h => ⟨h.1, h.2.2.1⟩,
        WP.mono (VG.Proof.MlDsa.X86_64.Sample.rnCmp_ok y) fun _ h => ⟨h.1, h.2.2.1⟩⟩)
      fun x y x' y' ⟨e1, e2, e3⟩ ⟨f1, g1⟩ ⟨f2, g2⟩ => ⟨by rw [f1, f2, e3], by rw [g1, g2, e1], by rw [g1, g2, e2]⟩) ?_
  exact RelCT.ite (fun x y h => h.1)
    (taintRel [.rbp, .rdi] (fun x y h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h.1.2.1, h.1.2.2]) c2)
    (taintRel [] VG.Proof.MlDsa.X86_64.Sample.nil_regs c3)

theorem ofNat64_toNat' {j : Nat} (h : j ≤ 256) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem mid_ct : RelCT isa VG.Proof.MlDsa.X86_64.Sample.RejNttCT.R1 (.ite .b rnTry (.block []))
    fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi := by
  refine RelCT.ite (fun x y ⟨aP, L, p1, p2, _⟩ => by
      show x.cf = y.cf; rw [p1.cf, p2.cf, p1.rdi, p2.rdi]) ?_ ?_
  · refine RelCT.postDep (F := fun (x x' : State) => ∀ aP L, VG.Proof.MlDsa.X86_64.Sample.TryPre x aP L →
        x'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.rnTryL L ((x.gpr .r8).setWidth 32).toNat).length ∧
        VG.Proof.MlDsa.Sample.Stored x'.mem aP (VG.Proof.MlDsa.X86_64.Sample.rnTryL L ((x.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] x.mem x'.mem ∧
        Keep [.rdi] x x')
      (RelCT.mono (VG.Proof.MlDsa.X86_64.Sample.RejNttCT.traceTry (by taint_decide) (by taint_decide) (by taint_decide)) (fun x y h => by
        obtain ⟨⟨aP, L, p1, p2, e8, _, _⟩, _⟩ := h
        exact ⟨by rw [p1.rbp, p2.rbp], by rw [p1.rdi, p2.rdi], by rw [e8]⟩) fun _ _ h => h) ?_ ?_
    · intro x y ⟨⟨aP, L, p1, p2, _⟩, hb⟩
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, VG.Proof.MlDsa.X86_64.Sample.RejNttCT.ofNat64_toNat' p1.len] at this; simpa using this
      exact ⟨VG.Proof.MlDsa.X86_64.Sample.RejNttCT.rnTry_all x ⟨aP, L, p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩,
        VG.Proof.MlDsa.X86_64.Sample.RejNttCT.rnTry_all y ⟨aP, L, p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩⟩
    · intro x y x' y' ⟨⟨aP, L, p1, p2, _, ecx, esi⟩, hb⟩ f1 f2
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, VG.Proof.MlDsa.X86_64.Sample.RejNttCT.ofNat64_toNat' p1.len] at this; simpa using this
      obtain ⟨_, _, _, k1⟩ := f1 aP L ⟨p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩
      obtain ⟨_, _, _, k2⟩ := f2 aP L ⟨p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩
      exact ⟨by rw [k1.gpr (by decide), k2.gpr (by decide), ecx], by rw [k1.gpr (by decide), k2.gpr (by decide), esi]⟩
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] VG.Proof.MlDsa.X86_64.Sample.nil_regs
      (by taint_decide)) (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, ecx, esi⟩, _⟩ f1 f2
    rw [f1, f2]; exact ⟨ecx, esi⟩

/-! ## An iteration -/

/-- The hypotheses of `rnBody_ok`. -/
structure BPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : VG.Proof.MlDsa.X86_64.Sample.CoeffsWr s.wr aP
  st : VG.Proof.MlDsa.Sample.Stored s.mem aP L
  r0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1
  r1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1
  r2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1

/-- Two runs at the start of an iteration, with the same coefficients sampled
and the same bytes to read. -/
def BRel (s₁ s₂ : State) : Prop :=
  ∃ aP L, VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BPre s₁ aP L ∧ VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BPre s₂ aP L ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    ∀ k < 3, s₁.mem (s₁.gpr .rsi + BitVec.ofNat 64 k) = s₂.mem (s₂.gpr .rsi + BitVec.ofNat 64 k)

theorem load_ct : RelCT isa VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BRel (.block rnLoad) VG.Proof.MlDsa.X86_64.Sample.RejNttCT.R1 := by
  refine RelCT.postDep (F := fun (x x' : State) =>
      (x'.gpr .r8 = BitVec.setWidth 64 (VG.Proof.MlDsa.X86_64.Sample.rnw (x.mem (x.gpr .rsi)) (x.mem (x.gpr .rsi + BitVec.ofNat 64 1))
          (x.mem (x.gpr .rsi + BitVec.ofNat 64 2))) ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧ x'.gpr .rdi = x.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .rdi] x x')
    (taintRel [.rsi] (fun x y ⟨_, _, _, _, esi, _⟩ r hr => by simp at hr; subst hr; exact esi) (by taint_decide))
    (fun x y ⟨_, _, p1, p2, _⟩ => ⟨VG.Proof.MlDsa.X86_64.Sample.rnLoad_ok x p1.r0 p1.r1 p1.r2, VG.Proof.MlDsa.X86_64.Sample.rnLoad_ok y p2.r0 p2.r1 p2.r2⟩) ?_
  intro x y x' y' ⟨aP, L, p1, p2, esi, ecx, eb⟩ ⟨⟨h8, hc, hm, hdi⟩, k⟩ ⟨⟨h8', hc', hm', hdi'⟩, k'⟩
  have e0 := eb 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at e0
  have mp : ∀ {s s' : State}, VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BPre s aP L → s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) →
      s'.mem = s.mem → s'.gpr .rdi = s.gpr .rdi → Keep [.rax, .rdx, .r8, .rdi] s s' → VG.Proof.MlDsa.X86_64.Sample.RejNttCT.MPre s' aP L :=
    fun {s s'} p c m d kk => ⟨by rw [kk.gpr (by decide), p.rbp], by rw [d, p.rdi], p.len, by rw [kk.2.2]; exact p.wr,
      by rw [m]; exact p.st, by rw [c, d]⟩
  exact ⟨aP, L, mp p1 hc hm hdi k, mp p2 hc' hm' hdi' k',
    by rw [h8, h8', e0, eb 1 (by decide), eb 2 (by decide)], by rw [k.gpr (by decide), k'.gpr (by decide), ecx],
    by rw [k.gpr (by decide), k'.gpr (by decide), esi]⟩

theorem step_ct : RelCT isa (fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi)
    (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]) fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.postDep (F := fun (x x' : State) => x'.zf = some (x.gpr .rcx - 1 == 0))
    (taintRel [] VG.Proof.MlDsa.X86_64.Sample.nil_regs (by taint_decide))
    (fun x y _ => ⟨WP.mono (VG.Proof.MlDsa.X86_64.Sample.step_ok x 3) fun _ h => h.1.2.2.1, WP.mono (VG.Proof.MlDsa.X86_64.Sample.step_ok y 3) fun _ h => h.1.2.2.1⟩)
    fun x y x' y' e f1 f2 => by rw [f1, f2, e.1]

theorem body_ct : RelCT isa VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BRel rnBody fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.seq VG.Proof.MlDsa.X86_64.Sample.RejNttCT.load_ct (RelCT.seq VG.Proof.MlDsa.X86_64.Sample.RejNttCT.mid_ct VG.Proof.MlDsa.X86_64.Sample.RejNttCT.step_ct)

end RejNttCT

/-! ## The whole function -/

namespace RejNtt

open RejNttCT

section
variable {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂)
include hq

theorem pub_X : VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ₁ = VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ₂ := by simp only [VG.Proof.MlDsa.X86_64.Sample.RejNtt.X, VG.Proof.MlDsa.X86_64.Sample.RejNtt.B, hq.2.2.2.2]
theorem pub_sp : VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ₁ = VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ₂ := by simp only [VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf, hq.1, hq.2.1, hq.2.2.1]
theorem pub_aP : σ₁.gpr .rsi = σ₂.gpr .rsi := hq.2.1
theorem pub_Lt (t : Nat) : VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ₁ t = VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ₂ t := by simp only [VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt, VG.Proof.MlDsa.X86_64.Sample.RejNtt.pub_X hq]

theorem spPub : VG.Proof.MlDsa.X86_64.Sample.SpPub (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ₁) (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ₂) σ₁ σ₂ :=
  ⟨hq.1, rfl, hq.2.2.1, hq.2.1, rfl, hq.2.2.2.1⟩

end

/-- Two runs at iteration `t`, `n = 336 - t` iterations from the end. -/
def LI (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, rnK.pre σ₁ ∧ rnK.pre σ₂ ∧ rnK.pub σ₁ σ₂ ∧ n = 336 - t ∧ t < 336 ∧ VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ₁ t s₁ ∧ VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ₂ t s₂

theorem bpre {σ : State} (hp : rnK.pre σ) {t : Nat} (ht : t < 336) {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ t s) :
    VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BPre s (σ.gpr .rsi) (VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ t) :=
  ⟨h.env.rbp, h.rdi, VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt_length_le t, .of_mem (by rw [h.env.wr, hp.2.1]; simp), h.stored,
    by simpa using VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_regions hp h (k := 0) (by omega), VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_regions hp h (by omega), VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_regions hp h (by omega)⟩

theorem li_brel {n : Nat} {s₁ s₂ : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejNtt.LI n s₁ s₂) : VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂⟩ := h
  refine ⟨σ₁.gpr .rsi, VG.Proof.MlDsa.X86_64.Sample.RejNtt.Lt σ₁ t, VG.Proof.MlDsa.X86_64.Sample.RejNtt.bpre p₁ ht l₁, by rw [VG.Proof.MlDsa.X86_64.Sample.RejNtt.pub_aP hq, VG.Proof.MlDsa.X86_64.Sample.RejNtt.pub_Lt hq]; exact VG.Proof.MlDsa.X86_64.Sample.RejNtt.bpre p₂ ht l₂,
    by rw [l₁.rsi, l₂.rsi, VG.Proof.MlDsa.X86_64.Sample.RejNtt.pub_sp hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [VG.Proof.MlDsa.X86_64.Sample.RejNtt.out_byte l₁ (by omega), VG.Proof.MlDsa.X86_64.Sample.RejNtt.out_byte l₂ (by omega), VG.Proof.MlDsa.X86_64.Sample.RejNtt.pub_X hq]

theorem loop_ct (n : Nat) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sample.RejNtt.LI n) (.loop rnBody .ne) (Rel2 rnK.pre rnK.pub fun σ s => VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ 336 s) := by
  refine RelCT.loop (M := isa) VG.Proof.MlDsa.X86_64.Sample.RejNtt.LI (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, rnK.pre p.1 ∧ p.2 < 336 ∧ VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt p.1 p.2 x →
      VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt p.1 (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (336 - p.2) - 1 == 0))
    (RelCT.mono VG.Proof.MlDsa.X86_64.Sample.RejNttCT.body_ct (fun x y h => VG.Proof.MlDsa.X86_64.Sample.RejNtt.li_brel h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all' (fun p hp' => VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (336 - t) - 1 == 0) = decide (t + 1 = 336) := by
      rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 336 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ 336 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨336 - (t + 1), by omega, σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega, l₁', l₂'⟩

/-- After the first block of the loop's setup. -/
def IA (σ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ s ∧ bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840) 1008 = VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ ∧ s.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840 ∧
    s.gpr .rdi = 0

theorem latB {σ s : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejNtt.IA σ s) : WP isa (.block [.mov32 .rcx (.imm 336)]) s (VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ 0) := by
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 336)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  exact ⟨h.1.keep hm2 (k2.mono (by decide)), by rw [hm2]; exact h.2.1, by rw [k2.gpr (by decide), h.2.2.1]; simp,
    by rw [k2.gpr (by decide), h.2.2.2]; rfl, hcx, by rw [hm2]; exact stored_nil _ _⟩

theorem hok : ∀ σ, rnK.pre σ → VG.Proof.MlDsa.X86_64.Sample.SpOk (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ := fun _ hp => VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOk hp

theorem hpub : ∀ σ₁ σ₂, rnK.pre σ₁ → rnK.pre σ₂ → rnK.pub σ₁ σ₂ → VG.Proof.MlDsa.X86_64.Sample.SpPub (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ₁) (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => VG.Proof.MlDsa.X86_64.Sample.RejNtt.spPub hq

/-- The loop and the end. -/
theorem tail_ct : RelCT isa (Rel2 rnK.pre rnK.pub fun σ => VG.Proof.MlDsa.X86_64.Sample.J6 168 1008 (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ)
    (.seq rnLoop (.block (retJ ++ VG.Impl.MlDsa.X86_64.Sample.epi))) fun _ _ => True := by
  refine RelCT.seq (RelCT.seq (relInv (I' := VG.Proof.MlDsa.X86_64.Sample.RejNtt.IA) (fun σ s _ h => VG.Proof.MlDsa.X86_64.Sample.RejNtt.lat0 h)
      (VG.Proof.MlDsa.X86_64.Sample.taintSp VG.Proof.MlDsa.X86_64.Sample.RejNtt.hpub (fun _ _ h => h.env) [] VG.Proof.MlDsa.X86_64.Sample.nil_regs (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ 0 s) (fun σ s _ h => VG.Proof.MlDsa.X86_64.Sample.RejNtt.latB h)
        (VG.Proof.MlDsa.X86_64.Sample.taintSp VG.Proof.MlDsa.X86_64.Sample.RejNtt.hpub (J := fun P σ s => VG.Proof.MlDsa.X86_64.Sample.Env P σ s ∧ bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840) 1008 = VG.Proof.MlDsa.X86_64.Sample.RejNtt.X σ ∧
          s.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ).at' 840 ∧ s.gpr .rdi = 0) (fun _ _ h => h.1) [] VG.Proof.MlDsa.X86_64.Sample.nil_regs (by taint_decide)))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ => ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by omega, l₁, l₂⟩)
      (VG.Proof.MlDsa.X86_64.Sample.RejNtt.loop_ct 336))) ?_
  exact VG.Proof.MlDsa.X86_64.Sample.taintSp VG.Proof.MlDsa.X86_64.Sample.RejNtt.hpub (J := fun P σ s => VG.Proof.MlDsa.X86_64.Sample.RejNtt.LAt σ 336 s) (fun _ _ h => h.env) [] VG.Proof.MlDsa.X86_64.Sample.nil_regs (by taint_decide)

end RejNtt

open RejNtt RejNttCT in
theorem rejNTT_ct : ConstantTime isa rnK.pre rnK.pub Impl.MlDsa.X86_64.Sample.rejNTT := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => VG.Proof.MlDsa.X86_64.Sample.J0 (VG.Proof.MlDsa.X86_64.Sample.RejNtt.spOf σ) σ)
    (fun σ s hp h => by subst h; exact VG.Proof.MlDsa.X86_64.Sample.RejNtt.pro_ok hp)
    (taintRel [.rdi, .rsi, .rdx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  exact RelCT.seq (VG.Proof.MlDsa.X86_64.Sample.sponge_ct VG.Proof.MlDsa.X86_64.Sample.RejNtt.hok VG.Proof.MlDsa.X86_64.Sample.RejNtt.hpub (.inr rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))
    VG.Proof.MlDsa.X86_64.Sample.RejNtt.tail_ct

end VG.Proof.MlDsa.X86_64.Sample

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

theorem leakBytes_inj : ∀ {a b : List Byte}, a.map (fun x => x.toNat) = b.map (fun x => x.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.X86_64.Sample.leakBytes_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A state satisfying the precondition. -/
def rnSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejNTT_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.rejNTT (Spec.MlDsa.rejNTTContract X86_64.abi 16) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Sample.rejNTT_correct VG.Proof.MlDsa.X86_64.Sample.rejNTT_ct
    { pre := by sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.X86_64.Sample.rnK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.X86_64.Sample.rnK, X86_64.abi, X86_64.argRegs]
        dsimp only [VG.Proof.MlDsa.X86_64.Sample.rnK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rnFold [] (VG.Spec.MlDsa.G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
            show Spec.MlDsa.rejNTTPoly 1008 _ = _
            rw [rejNTT_some hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.X86_64.Sample.rnK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx⟩ := h
        exact ⟨hdi, hsi, hdx, hsp, VG.Proof.MlDsa.X86_64.Sample.leakBytes_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, VG.Proof.MlDsa.X86_64.Sample.rnK, X86_64.abi,
        X86_64.argRegs] [rnSat] using VG.Proof.MlDsa.X86_64.Sample.rnSat }

end VG.Proof.MlDsa.X86_64.Sample

end
