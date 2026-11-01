module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Tail
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.BE64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.X25519.RISCV64.Instr

/-!
# Deterministic ECDSA on RISC-V: correctness

From the start of the frame's body: the prologue saves our caller's `ra` and
`s0`–`s5` and moves the pointers into `s0`–`s4` (`prologue_ok`, after which
`KR` holds); `h = bits2octets(digest)` (`reduce_ok`); `K = 0x00…` and
`V = 0x01…` (`initKV_ok`); then steps d–g (`rekeyFull_ok`), after which `K`
and `V` are RFC 6979's (`kv0_eq`). Before candidate `i`, they are those of
RFC 6979's search before it (`LoopInv`); a candidate is `V = HMAC_K(V)`,
whose number `core` reads as `k` (`cand_ok`, `coreAt_ok`), then whether to go
on (`goOn_ok`) and step h.3 or the end (`tryOne_ok`, `loop_ok`). The
candidate the loop stops at has RFC 6979's signature (`result_eq`). In its
frame, the function meets `rfcR` (`correct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_addSp)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.RISCV64 (WsReg addCall_ok CallKeep)
open VG.Proof.Mont (wordsVal Outside Outs)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {P : Rfc}

theorem add_ofNat_add' (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : bytesAt m p k = (bytesAt m p n).take k := by
  rw [show n = k + (n - k) by omega, VG.Proof.Hmac.Common.bytesAt_add, List.take_left' (bytesAt_length _ _ _)]

/-! ## The prologue -/

theorem prologue_eq : Cfg.prologue = .addSp .t0 0 :: (Spill.saveCode .t0 saved ++
    [mov .s1 .t0, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s0 .a3]) := rfl

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem prologue_ok : WP isa (.block Cfg.prologue) s₀ (KR P s₀) := by
  rw [prologue_eq]
  refine wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_
  have t0 : s₁.gpr .t0 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero]
  have e₁ : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  refine Spill.save_ok (b := .t0) (by rw [t0]; omega_using [hp.al])
    (fun q hq => by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun q hq => by
      rw [t0, u₁.wr]
      exact in_fr hp rfl (by have := saved_in q hq; simp only [frB]; omega)) ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    WP.block_nil ?_
  have mm : s₆.mem = Spill.saveMem s₁.mem s₀.sp s₁.gpr saved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    show Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr saved = _
    rw [t0]
  have gg : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s0] → s₆.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f⟩ := hr
    exact (u₆.other r f).trans ((u₅.other r d).trans ((u₄.other r c).trans ((u₃.other r b).trans (u₂.other r a))))
  have sv : Spill.Saved s₀.sp s₀.gpr saved s₆.mem := by
    rw [mm]
    intro q hq
    rw [Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact e₁ _ (by decide)
  refine ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd,
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr,
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_, sv, ?_⟩
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact t0
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · rw [gg q (by revert q; decide), e₁ q (by revert q hq; decide)]
  · rw [mm, u₁.mem]
    refine ((Spill.saveMem_frame_base (n := 64) (fun p hp' => (saved_in p hp').2) (by omega) _ _ _).sub
      fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR s₀, by simp, Region.sub_prefix (by simp only [frB]; omega)⟩

end

/-! ## `h = bits2octets(digest)` -/

/-- The values of the run: the private key and its bytes, the digest and its
integer, and `h`. -/
abbrev dB (s₀ : State) : List Byte := bytesAt s₀.mem (dk s₀) 32
abbrev xOf (s₀ : State) : Nat := Spec.Weierstrass.ofBytes (dB s₀)
abbrev hBOf (P : Rfc) (s₀ : State) : List Byte := bytesAt s₀.mem (dg s₀) P.c.H.D
abbrev eOf (P : Rfc) (s₀ : State) : Nat := Spec.Ecdsa.hashToInt Spec.P256.curve (hBOf P s₀)
abbrev hSpec (P : Rfc) (s₀ : State) : List Byte := Spec.Ecdsa.Rfc6979.bits2octets Spec.P256.curve (hBOf P s₀)

/-- `V` and `h` in the frame. -/
abbrev vOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fV) P.c.H.D
abbrev hOf (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fH) 32

/-- Changes within the working space are changes within `scratch`. -/
theorem frame_of_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) : Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  have hx' := hx _ (List.mem_singleton_self _)
  refine h x fun w hw => .inr ?_
  have := hW w hw
  simp only [Region.Contains] at hx'
  show w.1 + w.2 ≤ (x - base).toNat
  omega

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem ws_of {s : State} (h : KR P s₀ s) : WsReg s (scr s₀) :=
  ⟨h.s0, scr_wr hp h.wr, hp.nc, hp.ca⟩

/-- `KR` across code that writes only `scratch` and temporaries. -/
theorem KR.scr {s s' : State} (h : KR P s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hf : Frame [scrR s₀] s.mem s'.mem) :
    KR P s₀ s' :=
  h.keep hrd hwr hsp hg hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.f_c.sub_left (part_sub (by simp only [frB]; omega)))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun x hx => hx⟩)

/-- The digest's leftmost 32 bytes, the bytes apart from the working space. -/
theorem dg_out {i : Nat} (hi : i < 32) :
    ¬ (⟨scr s₀, 8192⟩ : Region).Contains (dg s₀ + BitVec.ofNat 64 (0 + i)) 1 :=
  Proof.Ecdh.RISCV64.P256.out_of_disj (n := 32) (hp.g_c.sub_left (Region.sub_prefix (by have := (sizes P).D; omega)))
    (by have := hp.ng; have := (sizes P).D; omega) (by omega)

theorem reduce_ok {s : State} (h : KR P s₀ s) :
    WP isa P.c.reduce s fun t => KR P s₀ t ∧ hOf s₀ t.mem = hSpec P s₀ ∧
      Frame [scrR s₀, sR s₀ fH 32] s.mem t.mem := by
  have hz := sizes P
  have hw := ws_of hp h
  unfold Cfg.reduce
  rw [P.hFN]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Weierstrass.RISCV64.loadNum_ok 4 hw (o := sX) (p := .s4) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by
      rw [h.s4]
      exact Proof.Ecdh.RISCV64.P256.in_rd8 (rs := s.rd ++ s.wr) (n := P.c.H.D)
        (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)) (by have := hz.D; omega) (by have := hz.D; omega))
    (fun i hi => by rw [h.s4]; exact dg_out hp hi)) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_
  have hw₁ := hw.of_rest r₁
  refine WP.mono (VG.Proof.Weierstrass.RISCV64.setConst_ok 4 hw₁ (o := sZ) (x := 0) (by decide) (by decide))
    fun s₂ ⟨r₂, O₂, e₂⟩ => ?_
  have hw₂ := hw₁.of_rest r₂
  have x₂ : wordsVal s₂.mem (scr s₀) sX 4 = Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) 32) := by
    rw [O₂.unch.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; decide) (by decide), e₁,
      h.s4, BitVec.add_zero]
    exact congrArg _ (h.dgBytes hp (n := 32) (by have := hz.D; omega))
  have hx : Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) 32) < 2 ^ 256 := by
    have := VG.Proof.Ecdsa.Rfc6979.ofBytes_lt (bytesAt s₀.mem (dg s₀) 32)
    rwa [bytesAt_length] at this
  refine WP.seq (WP.mono (addCall_ok VG.Proof.Ecdsa.RISCV64.P256.order_ok hw₂ (o := sY) (a := sX) (b := sZ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      show wordsVal s₂.mem (scr s₀) sX 4 + wordsVal s₂.mem (scr s₀) sZ 4 < 2 * Spec.P256.curve.n
      rw [x₂, e₂]
      have : 2 ^ 256 < 2 * Spec.P256.curve.n := by decide
      simp only [Nat.zero_mod, Nat.add_zero]; omega)) fun s₃ ⟨C₃, v₃⟩ => ?_)
  have v₃' : wordsVal s₃.mem (scr s₀) sY 4 =
      (wordsVal s₂.mem (scr s₀) sX 4 + wordsVal s₂.mem (scr s₀) sZ 4) % Spec.P256.curve.n := v₃
  have hw₃ := hw₂.of_kp C₃.kp
  refine VG.RISCV64.BE64.wp_li_int (imm := -1) (by decide) fun s₄ u₄ => ?_
  have a7 : s₄.gpr .a7 = VG.Proof.Weierstrass.RISCV64.maskOf true := by rw [u₄.gpr]; decide
  have hw₄ : WsReg s₄ (scr s₀) := ⟨by rw [u₄.other _ (by decide)]; exact hw₃.s0, by rw [u₄.wr]; exact hw₃.wr,
    hw₃.nowrap, hw₃.al⟩
  -- the registers and regions so far
  have g₄ : ∀ r ∈ kregs, s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r (by revert r; decide), C₃.kp.gpr r (kregs_pres r hr), r₂.gpr r (by revert r; decide),
      r₁.gpr r (by revert r; decide)]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, C₃.kp.rd, r₂.rd, r₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, C₃.kp.wr, r₂.wr, r₁.wr]
  have sp₄ : s₄.sp = s.sp := by rw [u₄.sp, C₃.kp.sp, r₂.sp, r₁.sp]
  have U₄ : Unch (scr s₀) ([(sX, 32)] ++ [(sZ, 32)] ++ [(sY, 32), (3840, 256)]) s.mem s₄.mem := by
    rw [u₄.mem]
    exact (O₁.unch.trans O₂.unch).trans C₃.mem
  have F₄ : Frame [scrR s₀] s.mem s₄.mem := frame_of_unch U₄ (by decide)
  have K₄ : KR P s₀ s₄ := KR.scr hp h rd₄ wr₄ sp₄ g₄ F₄
  have q₄ : s₄.gpr .s1 = s₀.sp := K₄.s1
  refine WP.mono (VG.Proof.Weierstrass.RISCV64.storeNum_ok true 4 hw₄ a7 (q := .s1) (a := sY) (off := fH) (by decide)
    (by decide) (by decide) (by decide)
    (fun i hi => by rw [q₄]; exact in_fr hp K₄.wr (o := fH + i) (n := 1) (by simp only [fH, frB]; omega))
    (fun i hi => by
      rw [q₄]
      refine Proof.Ecdh.RISCV64.P256.out_of_disj (n := frB) hp.f_c (by have := hp.top; simp only [frB] at *; omega)
        (by simp only [fH, frB]; omega))) fun s₅ ⟨r₅, m₅⟩ => ?_
  have v₄ : wordsVal s₄.mem (scr s₀) sY 4 = Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) 32) % Spec.P256.curve.n := by
    rw [u₄.mem, v₃', x₂, e₂]
    simp only [Nat.zero_mod, Nat.add_zero]
  have F₅ : Frame [sR s₀ fH 32] s₄.mem s₅.mem := by
    rw [m₅, q₄]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.Weierstrass.length_toBytes]; exact Region.contains_self _ _)
  refine ⟨K₄.keep r₅.rd r₅.wr r₅.sp (fun r hr => r₅.gpr r (by revert r; decide)) F₅
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by decide)) (by decide) (by decide))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, part_sub (by decide)⟩), ?_, ?_⟩
  · simp only [m₅, q₄, ↓reduceIte, v₄]
    have e := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₄.mem (sA s₀ fH)
      (Spec.Weierstrass.toBytes 32 (Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) 32) % Spec.P256.curve.n))
      (by rw [VG.Proof.Weierstrass.length_toBytes]; decide)
    rw [VG.Proof.Weierstrass.length_toBytes] at e
    show bytesAt _ (s₀.sp + BitVec.ofNat 64 fH) 32 = _
    rw [e, hSpec, VG.Proof.Ecdsa.Rfc6979.bits2octets_eq (by rw [bytesAt_length]; exact hz.D.1)]
    rw [← bytesAt_take _ _ hz.D.1]
    rfl
  · refine (F₄.sub fun r hr => ?_).trans (F₅.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun x hx => hx⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨sR s₀ fH 32, by simp, fun x hx => hx⟩

end

/-! ## Bytes stored in the frame -/

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- `storeBytes` of the bytes `bs` (each below 256) to the frame at `doff`,
after the save area. -/
theorem store_ok {s : State} (h : KR P s₀ s) {doff : Nat} {bs : List Nat} (hb : ∀ i < bs.length, bs.getD i 0 < 256)
    (hd : 64 ≤ doff ∧ doff + bs.length ≤ frB) :
    WP isa (.block (Impl.Words.RISCV64.storeBytes .t0 .s1 doff bs)) s fun t => KR P s₀ t ∧
      bytesAt t.mem (sA s₀ doff) bs.length = bs.map (BitVec.ofNat 8) ∧ Frame [sR s₀ doff bs.length] s.mem t.mem ∧
      ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hfr : frB = 224 := rfl
  refine WP.mono (VG.RISCV64.Bytes.storeBytes_ok (s := s) (tmp := .t0) (dst := .s1) (doff := doff) (bs := bs)
    (by decide) (fun i hi => by have := hb i hi; omega) (by omega)
    (fun i hi => by rw [h.s1]; exact in_fr hp h.wr (o := doff + i) (n := 1) (by omega)))
    fun t ht => ?_
  have e : s.gpr .s1 + BitVec.ofNat 64 doff = sA s₀ doff := by rw [h.s1]
  have F : Frame [sR s₀ doff bs.length] s.mem t.mem := by have := ht.frame; rwa [e] at this
  refine ⟨h.keep ht.rd ht.wr ht.sp (fun r hr => ht.gpr r (by revert r; decide)) F
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl hd.1) (by omega) (by omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hd.2⟩), ?_, F,
    fun r hr => ht.gpr r (fun e => by subst e; exact absurd hr (by decide))⟩
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [show sA s₀ doff + BitVec.ofNat 64 i = s.gpr .s1 + BitVec.ofNat 64 (doff + i) by
    rw [← e, add_ofNat_add'], ht.stored i (by simpa [bytesAt] using h₁)]
  simp only [List.length_map] at h₂
  simp [List.getD_eq_getElem?_getD, h₂]

end

/-! ## Steps b–g and h.3 -/

/-- Bytes apart from what changed. -/
theorem fbytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

/-- `KR`, with `K`, `V` and `h`. -/
structure KVH (P : Rfc) (s₀ : State) (K V : List Byte) (t : State) : Prop where
  kr : KR P s₀ t
  k : kOf P s₀ t.mem = K
  v : vOf P s₀ t.mem = V
  h : hOf s₀ t.mem = hSpec P s₀

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- A part of the frame apart from what an HMAC writes, the MAC at `dst` but. -/
theorem hd_apart {o n dst : Nat} (h : o + n ≤ frB) (hd : o + n ≤ dst ∨ dst + P.c.H.D ≤ o) (hdst : dst + P.c.H.D ≤ frB) :
    ∀ r ∈ [stR s₀, sR s₀ dst P.c.H.D, stk P s₀], Region.Disjoint (sR s₀ o n) r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact fr_st hp h (fun x hx => hx)
  · exact part_disj hd (by simp only [frB] at h; omega) (by simp only [frB] at hdst; omega)
  · exact (f_s hp).sub_left (part_sub h)

theorem initKV_ok {s : State} (h : KR P s₀ s) (hh : hOf s₀ s.mem = hSpec P s₀) :
    WP isa (.block P.c.initKV) s (KVH P s₀ (List.replicate P.c.H.D 0) (List.replicate P.c.H.D 1)) := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.initKV
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hp h (doff := fK) (bs := List.replicate P.c.H.D 0) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fK, frB, List.length_replicate]; omega)) fun t₁ ⟨k₁, b₁, f₁, _⟩ => ?_
  refine WP.mono (store_ok hp k₁ (doff := fV) (bs := List.replicate P.c.H.D 1) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fV, frB, List.length_replicate]; omega)) fun t₂ ⟨k₂, b₂, f₂, _⟩ => ?_
  simp only [List.length_replicate, List.map_replicate] at b₁ b₂ f₁ f₂
  have hn : P.c.H.D ≤ 2 ^ 64 := by omega
  refine ⟨k₂, ?_, b₂, ?_⟩
  · show bytesAt t₂.mem (sA s₀ fK) P.c.H.D = _
    rw [fbytes f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fK, fV]; omega)) (by simp only [fK]; omega) (by simp only [fV]; omega)) hn, b₁]
    rfl
  · show bytesAt t₂.mem (sA s₀ fH) 32 = _
    rw [fbytes f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by simp only [fH, fV]; omega)) (by simp only [fH]; omega) (by simp only [fV]; omega))
      (by omega),
      fbytes f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by simp only [fH, fK]; omega)) (by simp only [fH]; omega) (by simp only [fK]; omega))
      (by omega)]
    exact hh

/-- The separator `b` after `V`: the first part of the messages. -/
theorem sep_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) {b : Nat} (hb : b < 256) :
    WP isa (.block (P.c.sep b)) s fun t => KVH P s₀ K V t ∧
      bytesAt t.mem (sA s₀ fV) (P.c.H.D + 1) = V ++ [BitVec.ofNat 8 b] ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.sep
  refine WP.mono (store_ok hp h.kr (doff := fV + P.c.H.D) (bs := [b]) (fun i hi => by
      simp only [List.length_singleton] at hi; obtain rfl : i = 0 := by omega
      simpa using hb)
    (by simp only [fV, frB, List.length_singleton]; omega)) fun t ⟨k, bt, f, pr⟩ => ?_
  simp only [List.length_singleton, List.map_cons, List.map_nil] at bt f
  have hv : vOf P s₀ t.mem = V := by
    rw [← h.v]
    exact fbytes f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by omega)) (by simp only [fV]; omega) (by simp only [fV]; omega)) (by omega)
  refine ⟨⟨k, ?_, hv, ?_⟩, ?_, pr⟩
  · rw [← h.k]
    exact fbytes f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fK, fV]; omega)) (by simp only [fK]; omega) (by simp only [fV]; omega))
      (by omega)
  · rw [← h.h]
    exact fbytes f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by simp only [fH, fV]; omega)) (by simp only [fH]; omega) (by simp only [fV]; omega))
      (by omega)
  · rw [VG.Proof.Hmac.Common.bytesAt_add, show bytesAt t.mem (sA s₀ fV) P.c.H.D = V from hv]
    rw [show sA s₀ fV + BitVec.ofNat 64 P.c.H.D = sA s₀ (fV + P.c.H.D) from add_ofNat_add' _ _ _, bt]

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) :
    WP isa P.c.hmacV s fun t => KVH P s₀ K (Spec.Hmac.hmac P.hH.SH.H K V) t ∧
      ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.hmacV
  refine WP.mono (hmac_ok hp h.kr (ps := [(.s1, fV, P.c.H.D)]) (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, frB]; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := fV) ⟨by simp only [fV]; omega, by simp only [fV, frB]; omega⟩) fun t ⟨k, hv, f, pr⟩ => ?_
  have hm : msgOf s.mem s₀ [(.s1, fV, P.c.H.D)] = V := by
    simp only [msgOf, List.append_nil]; exact h.v
  refine ⟨⟨k, ?_, ?_, ?_⟩, pr⟩
  · rw [← h.k]
    exact fbytes f (hd_apart hp (by simp only [fK, frB]; omega) (.inl (by simp only [fK, fV]; omega))
      (by simp only [fV, frB]; omega)) (by omega)
  · show bytesAt t.mem (sA s₀ fV) P.c.H.D = _
    rw [hv, hm, h.k]
  · rw [← h.h]
    exact fbytes f (hd_apart hp (by simp only [fH, frB]; omega) (.inr (by simp only [fH, fV]; omega))
      (by simp only [fV, frB]; omega)) (by omega)

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) {b : Nat} (hb : b < 256) :
    WP isa (P.c.rekeyFull b) s fun t =>
      let K' := Spec.Hmac.hmac P.hH.SH.H K (V ++ BitVec.ofNat 8 b :: (dB s₀ ++ hSpec P s₀))
      KVH P s₀ K' (Spec.Hmac.hmac P.hH.SH.H K' V) t := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.rekeyFull
  refine WP.seq (WP.mono (sep_ok hp h hb) fun s₁ ⟨h₁, m₁, _⟩ => ?_)
  refine WP.seq (WP.mono (hmac_ok hp h₁.kr (ps := [(.s1, fV, P.c.H.D + 1), (.s3, 0, 32), (.s1, fH, 32)])
    (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      · exact .inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, frB]; omega⟩
      · exact .inr ⟨rfl, rfl, Nat.le_refl _⟩
      · exact .inl ⟨rfl, by simp only [fH]; omega, by simp only [fH, frB]; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := fK) ⟨by decide, by simp only [fK, frB]; omega⟩) fun t ⟨k, hk, f, pr⟩ => ?_)
  have hm : msgOf s₁.mem s₀ [(.s1, fV, P.c.H.D + 1), (.s3, 0, 32), (.s1, fH, 32)] =
      V ++ BitVec.ofNat 8 b :: (dB s₀ ++ hSpec P s₀) := by
    simp only [msgOf, List.append_nil, pA, regV]
    rw [m₁, BitVec.add_zero, h₁.kr.dBytes hp]
    have hh := h₁.h
    simp only [hOf] at hh
    rw [hh]
    simp
  refine WP.mono (hmacV_ok hp (K := Spec.Hmac.hmac P.hH.SH.H K (V ++ BitVec.ofNat 8 b :: (dB s₀ ++ hSpec P s₀)))
    (V := V) ⟨k, ?_, ?_, ?_⟩) fun u hu => hu.1
  · show bytesAt t.mem (sA s₀ fK) P.c.H.D = _
    rw [hk, hm, h₁.k]
  · rw [← h₁.v]
    exact fbytes f (hd_apart hp (by simp only [fV, frB]; omega) (.inr (by simp only [fK, fV]; omega))
      (by simp only [fK, frB]; omega)) (by omega)
  · rw [← h₁.h]
    exact fbytes f (hd_apart hp (by simp only [fH, frB]; omega) (.inr (by simp only [fH, fK]; omega))
      (by simp only [fK, frB]; omega)) (by omega)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) :
    WP isa P.c.rekey s (fun t => KVH P s₀ (Spec.Ecdsa.Rfc6979.next P.hH.SH.H K V).1
      (Spec.Ecdsa.Rfc6979.next P.hH.SH.H K V).2 t ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r) := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.rekey
  refine WP.seq (WP.mono (sep_ok hp h (b := 0) (by decide)) fun s₁ ⟨h₁, m₁, pr₁⟩ => ?_)
  refine WP.seq (WP.mono (hmac_ok hp h₁.kr (ps := [(.s1, fV, P.c.H.D + 1)])
    (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, frB]; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := fK) ⟨by decide, by simp only [fK, frB]; omega⟩) fun t ⟨k, hk, f, pr⟩ => ?_)
  refine WP.mono (hmacV_ok hp (K := Spec.Hmac.hmac P.hH.SH.H K (V ++ [0])) (V := V) ⟨k, ?_, ?_, ?_⟩)
    fun u hu => ⟨hu.1, fun r hr => (hu.2 r hr).trans ((pr r hr).trans (pr₁ r hr))⟩
  · show bytesAt t.mem (sA s₀ fK) P.c.H.D = _
    rw [hk]
    simp only [msgOf, List.append_nil, pA, regV]
    rw [m₁, h₁.k]
    rfl
  · rw [← h₁.v]
    exact fbytes f (hd_apart hp (by simp only [fV, frB]; omega) (.inr (by simp only [fK, fV]; omega))
      (by simp only [fK, frB]; omega)) (by omega)
  · rw [← h₁.h]
    exact fbytes f (hd_apart hp (by simp only [fH, frB]; omega) (.inr (by simp only [fH, fK]; omega))
      (by simp only [fK, frB]; omega)) (by omega)

end

/-! ## The candidates -/

/-- `K` and `V` after steps b–g, before candidate `i`, candidate `i`'s `V`,
and its signature. -/
abbrev kv0 (P : Rfc) (s₀ : State) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init Spec.P256.curve P.hH.SH.H P.c.H.D (xOf s₀) (hBOf P s₀)
abbrev kvI (P : Rfc) (s₀ : State) (i : Nat) : List Byte × List Byte :=
  VG.Proof.Ecdsa.Rfc6979.kvAt P.hH.SH.H (kv0 P s₀).1 (kv0 P s₀).2 i
abbrev candI (P : Rfc) (s₀ : State) (i : Nat) : List Byte :=
  VG.Proof.Ecdsa.Rfc6979.candAt P.hH.SH.H (kv0 P s₀).1 (kv0 P s₀).2 i
abbrev sigI (P : Rfc) (s₀ : State) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith Spec.P256.curve (xOf s₀) (eOf P s₀)
    (Spec.Ecdsa.Rfc6979.bits2int Spec.P256.curve (candI P s₀ i ++ []))

/-- Before candidate `i`. -/
structure LoopInv (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  kvh : KVH P s₀ (kvI P s₀ i).1 (kvI P s₀ i).2 t
  cnt : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P s₀ j = none

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (s₀ : State) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => t.gpr .a0 = 1 ∧ bytesAt t.mem (out s₀) 64 = Spec.Ecdsa.encode Spec.P256.curve rs
  | none => t.gpr .a0 = 0 ∧ bytesAt t.mem (out s₀) 64 = List.replicate 64 0

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  kr : KR P s₀ t
  fails : ∀ j < i, sigI P s₀ j = none
  last : sigI P s₀ i ≠ none ∨ i + 1 = P.c.tries
  res : ResultIs s₀ (sigI P s₀ i) t

theorem ResultIs.keep {s₀ : State} {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs s₀ r t)
    (ha : t'.gpr .a0 = t.gpr .a0) (hm : bytesAt t'.mem (out s₀) 64 = bytesAt t.mem (out s₀) 64) :
    ResultIs s₀ r t' := by
  unfold ResultIs at *
  split at h <;> exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- What `core` reads is candidate `i`'s signature's input. -/
theorem sg_eq {t : State} (hk : KR P s₀ t) {i : Nat} (hv : vOf P s₀ t.mem = candI P s₀ i) :
    VG.Proof.Ecdsa.RISCV64.P256.sg t.mem (dk s₀) (dg s₀) (sA s₀ fV) = sigI P s₀ i := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  simp only [VG.Proof.Ecdsa.RISCV64.P256.sg, sigI, VG.Proof.Ecdsa.Rfc6979.ecdsa_bytesAt]
  have hl : (candI P s₀ i).length = P.c.H.D := by rw [← hv, bytesAt_length]
  congr 1
  · exact congrArg _ (hk.dBytes hp)
  · rw [eOf, hk.dgBytes hp (n := 32) (by omega), VG.Proof.Ecdsa.Rfc6979.hashToInt_32 (bytesAt_length _ _ _),
      VG.Proof.Ecdsa.Rfc6979.hashToInt_take (by rw [bytesAt_length]; omega), ← bytesAt_take _ _ hD1]
  · rw [Spec.Ecdsa.Rfc6979.bits2int, List.append_nil, VG.Proof.Ecdsa.Rfc6979.hashToInt_take (by omega), ← hv,
      ← bytesAt_take _ _ hD1]

/-- `core`'s arguments. -/
theorem coreArgs_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) :
    WP isa (.block Cfg.coreArgs) t fun u => KVH P s₀ K V u ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      CoreArgs u (out s₀) (dk s₀) (dg s₀) (sA s₀ fV) (scr s₀) := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.coreArgs
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_addi (by decide) fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ?_
  have mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₅ : KR P s₀ s₅ := (((((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd
    (by decide) u₄).upd (by decide) u₅)
  have kS : Region.Sub ⟨sA s₀ fV, 32⟩ (frR s₀) := part_sub (by decide)
  have gS : Region.Sub ⟨dg s₀, 32⟩ (dgR P s₀) := Region.sub_prefix (by omega)
  have hk32 : (sA s₀ fV).toNat + 32 ≤ 2 ^ 64 := by
    have := hp.top
    show (s₀.sp + BitVec.ofNat 64 fV).toNat + 32 ≤ 2 ^ 64
    rw [VG.Offset.toNat_add_ofNat]; simp only [fV, frB] at *; omega
  refine ⟨⟨k₅, by rw [mm]; exact h.k, by rw [mm]; exact h.v, by rw [mm]; exact h.h⟩, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_,
    hp.o_c, hp.d_c, hp.g_c.sub_left gS, hp.f_c.sub_left kS, hp.no, hp.nd,
    by have := hp.ng; omega, hk32, hp.nc, hp.ca, ?_, ?_⟩
  · rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
      u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.kr.s2
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.kr.s3
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.kr.s4
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    exact h.kr.s0
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨dR s₀, List.mem_append_left _ (by rw [k₅.rd, hp.rd]; simp), 0, by simp, by simp⟩
    · exact ⟨dgR P s₀, List.mem_append_left _ (by rw [k₅.rd, hp.rd]; simp), 0, by simp, by simp only; omega⟩
    · exact cov_fr hp k₅ (o := fV) (n := 32) (by decide)
    · exact ⟨outR s₀, List.mem_append_right _ (out_wr hp k₅.wr), 0, by simp, by simp⟩
    · exact cov_scr hp k₅ (o := 0) (n := 8192) (by decide) |>.imp fun r' ⟨hm, off, hb, hl⟩ =>
        ⟨hm, off, by rw [← hb]; simp, hl⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨outR s₀, out_wr hp k₅.wr, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, scr_wr hp k₅.wr, 0, by simp, by simp⟩

/-- `core` with candidate `i`. -/
theorem coreCall_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) {i : Nat} (hv : V = candI P s₀ i)
    (ha : CoreArgs t (out s₀) (dk s₀) (dg s₀) (sA s₀ fV) (scr s₀)) :
    WP isa (.call P.c.coreN P.c.coreC) t fun u => KVH P s₀ K V u ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      ResultIs s₀ (sigI P s₀ i) u := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  rw [P.hcC]
  refine core_call P.law ha fun u a hpost => ?_
  have hw : ∀ r ∈ [(⟨out s₀, 64⟩ : Region), ⟨scr s₀, 8192⟩], Wk P s₀ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl fun x hx => hx)
    · exact .inr (.inr (.inl fun x hx => hx))
  have kp : ∀ {o n : Nat}, o + n ≤ frB → ∀ r ∈ [(⟨out s₀, 64⟩ : Region), ⟨scr s₀, 8192⟩],
      Region.Disjoint (sR s₀ o n) r := fun ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.f_o.sub_left (part_sub ho)
    · exact hp.f_c.sub_left (part_sub ho)
  refine ⟨⟨h.kr.call hp a.rd a.wr a.sp a.cs a.frame hw, ?_, ?_, ?_⟩, a.cs, ?_⟩
  · rw [← h.k]; exact fbytes a.frame (kp (by simp only [fK, frB]; omega)) (by omega)
  · rw [← h.v]; exact fbytes a.frame (kp (by simp only [fV, frB]; omega)) (by omega)
  · rw [← h.h]; exact fbytes a.frame (kp (by decide)) (by omega)
  · rw [sg_eq hp h.kr (by rw [h.v, hv])] at hpost
    unfold ResultIs
    exact hpost

end

/-! ## One candidate, and the loop -/

theorem sub_one_ofNat {k : Nat} (h₁ : 1 ≤ k) (h₂ : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem nonzero_ofNat {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  rw [bne, VG.RISCV64.Steps.ofNat_beq_zero h]
  simp

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
/-- One candidate fewer, and whether to go on. -/
theorem goOn_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) {i : Nat} (hi : i < P.c.tries)
    (hc : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)) (hr : ResultIs s₀ (sigI P s₀ i) t) :
    WP isa (.block Cfg.goOn) t fun u => KVH P s₀ K V u ∧ ResultIs s₀ (sigI P s₀ i) u ∧
      u.gpr .s5 = BitVec.ofNat 64 (P.c.tries - (i + 1)) ∧
      isa.eval (.nonzero .t6) u = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) := by
  have hT := P.hT'
  unfold Cfg.goOn
  refine VG.RISCV64.Steps.wp_subi (imm := 1) (by decide) fun s₁ u₁ =>
    VG.RISCV64.Steps.wp_andi (imm := 1) (by decide) fun s₂ u₂ =>
    VG.RISCV64.Steps.wp_subi (imm := 1) (by decide) fun s₃ u₃ =>
    VG.Proof.X25519.RISCV64.wp_and fun s₄ u₄ => WP.block_nil ?_
  have mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₄ : KR P s₀ s₄ := ((((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄)
  have c₄ : s₄.gpr .s5 = BitVec.ofNat 64 (P.c.tries - (i + 1)) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hc,
      sub_one_ofNat (by omega) (by omega), show P.c.tries - i - 1 = P.c.tries - (i + 1) by omega]
  have a₄ : s₄.gpr .a0 = t.gpr .a0 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have t6 : s₄.gpr .t6 = ((t.gpr .a0 &&& BitVec.ofInt 64 1) - BitVec.ofNat 64 1) &&& s₄.gpr .s5 := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other .a0 (by decide), c₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hc, sub_one_ofNat (by omega) (by omega), show P.c.tries - i - 1 = P.c.tries - (i + 1) by omega]
  refine ⟨⟨k₄, by rw [mm]; exact h.k, by rw [mm]; exact h.v, by rw [mm]; exact h.h⟩,
    hr.keep a₄ (by rw [mm]), c₄, ?_⟩
  rw [VG.RISCV64.Steps.eval_nonzero, t6, c₄]
  unfold ResultIs at hr
  split at hr
  · rename_i rs hs
    rw [hr.1, hs]
    have e : ((1 : BitVec 64) &&& BitVec.ofInt 64 1) - BitVec.ofNat 64 1 = 0 := by decide
    rw [e]
    simp
  · rename_i hs
    rw [hr.1, hs]
    have e : ((0 : BitVec 64) &&& BitVec.ofInt 64 1) - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide
    rw [e, BitVec.allOnes_and, nonzero_ofNat (by omega)]
    simp only [true_and]
    congr 1
    exact decide_eq_decide.mpr (by omega)

/-- One candidate: on, before the next, or the end. -/
theorem tryOne_ok {t : State} {i : Nat} (h : LoopInv P s₀ i t) :
    WP isa P.c.tryOne t fun u =>
      isa.eval (.nonzero .t6) u = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) ∧
      (sigI P s₀ i = none ∧ i + 1 < P.c.tries → LoopInv P s₀ (i + 1) u) ∧
      (¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) → Exit P s₀ i u) := by
  unfold Cfg.tryOne
  refine WP.seq (WP.mono (hmacV_ok hp h.kvh) fun t₁ ⟨k₁, p₁⟩ => ?_)
  refine WP.seq (WP.mono (coreArgs_ok hp k₁) fun t₂ ⟨k₂, p₂, a₂⟩ => ?_)
  refine WP.seq (WP.mono (coreCall_ok hp k₂ (i := i) rfl a₂) fun t₃ ⟨k₃, p₃, r₃⟩ => ?_)
  have c₃ : t₃.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i) := by
    rw [p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide), h.cnt]
  refine WP.seq (WP.mono (goOn_ok k₃ h.lt c₃ r₃) fun t₄ ⟨k₄, r₄, c₄, e₄⟩ => ?_)
  refine WP.ite _ e₄ (fun hg => ?_) fun hg => ?_
  · obtain ⟨hn, hlt⟩ := of_decide_eq_true hg
    refine WP.seq (WP.mono (rekey_ok hp k₄) fun t₅ ⟨k₅, p₅⟩ => ?_)
    refine wp_li (imm := 1) (by decide) fun t₆ u₆ => WP.block_nil ⟨?_, fun _ => ?_, fun hn' => absurd ⟨hn, hlt⟩ hn'⟩
    · rw [VG.RISCV64.Steps.eval_nonzero, u₆.gpr, decide_eq_true ⟨hn, hlt⟩]; rfl
    · have m₆ : t₆.mem = t₅.mem := u₆.mem
      refine ⟨hlt, ⟨k₅.kr.upd (by decide) u₆, by rw [m₆]; exact k₅.k, by rw [m₆]; exact k₅.v,
        by rw [m₆]; exact k₅.h⟩, ?_, fun j hj => ?_⟩
      · rw [u₆.other _ (by decide), p₅ _ (by decide), c₄]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h.fails j hj
        · exact hn
  · have hl : ¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) := of_decide_eq_false hg
    refine wp_li (imm := 0) (by decide) fun t₅ u₅ => WP.block_nil ⟨?_, fun h' => absurd h' hl, fun _ => ?_⟩
    · rw [VG.RISCV64.Steps.eval_nonzero, u₅.gpr, decide_eq_false hl]; rfl
    · refine ⟨h.lt, k₄.kr.upd (by decide) u₅, h.fails, ?_, r₄.keep (u₅.other _ (by decide)) (by rw [u₅.mem])⟩
      by_cases hs : sigI P s₀ i = none
      · have h1 := h.lt
        have h2 : ¬ i + 1 < P.c.tries := fun h' => hl ⟨hs, h'⟩
        exact .inr (by omega)
      · exact .inl hs

/-- The candidates, from the first: the loop stops at one. -/
theorem loop_ok {t : State} (h : LoopInv P s₀ 0 t) :
    WP isa (.loop P.c.tryOne (.nonzero .t6)) t fun u => ∃ i, Exit P s₀ i u := by
  refine WP.loop (M := isa) (fun n u => ∃ i, n = P.c.tries - i ∧ LoopInv P s₀ i u) ?_ _ t ⟨0, rfl, h⟩
  rintro n u ⟨i, rfl, hi⟩
  refine WP.mono (tryOne_ok hp hi) fun w ⟨he, hon, hoff⟩ => ?_
  by_cases hg : sigI P s₀ i = none ∧ i + 1 < P.c.tries
  · have hl := hon hg
    exact .inr ⟨by rw [he, decide_eq_true hg], _, by have := hl.lt; omega, i + 1, rfl, hl⟩
  · exact .inl ⟨by rw [he, decide_eq_false hg], i, hoff hg⟩

end

/-! ## Steps a–g, and the end -/

theorem restorable : Spill.Restorable .s1 restList := by decide

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : Rfc) (s₀ : State) :
    kv0 P s₀ =
      let K₁ := Spec.Hmac.hmac P.hH.SH.H (List.replicate P.c.H.D 0)
        (List.replicate P.c.H.D 1 ++ BitVec.ofNat 8 0 :: (dB s₀ ++ hSpec P s₀))
      let V₁ := Spec.Hmac.hmac P.hH.SH.H K₁ (List.replicate P.c.H.D 1)
      let K₂ := Spec.Hmac.hmac P.hH.SH.H K₁ (V₁ ++ BitVec.ofNat 8 1 :: (dB s₀ ++ hSpec P s₀))
      (K₂, Spec.Hmac.hmac P.hH.SH.H K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets Spec.P256.curve (xOf s₀) = dB s₀ := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, VG.Proof.Ecdsa.Rfc6979.rlen_p256,
      show (32 : Nat) = (dB s₀).length from (bytesAt_length _ _ _).symm, VG.Proof.Ecdsa.Rfc6979.toBytes_ofBytes]
  simp only [kv0, Spec.Ecdsa.Rfc6979.init, hi]
  rfl

theorem stores_ok {s₀ : State} (hp : Pre P s₀) : ∀ (l : List Nat) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ j ∈ l, j < 20) → KR P s₀ s →
    (∀ t, KR P s₀ t → t.gpr = s.gpr → Frame [sR s₀ fK 160] s.mem t.mem → WP isa (.block rest) t Q) →
    WP isa (.block (l.map (fun j => .store .d .t0 .s1 (fK + 8 * j)) ++ rest)) s Q
  | [], s, rest, Q, _, h, k => k s h rfl (Frame.refl _ _)
  | j :: l, s, rest, Q, hl, h, k => by
    have hj := hl j (by simp)
    simp only [List.map_cons, List.cons_append]
    refine VG.RISCV64.Steps.wp_sd (a := sA s₀ (fK + 8 * j)) (by simp only [fK]; omega) (by rw [h.s1])
      (by
        show (s₀.sp + BitVec.ofNat 64 (fK + 8 * j)).toNat % 8 = 0
        rw [VG.Offset.toNat_add_ofNat]
        have := hp.al; have := hp.top
        simp only [fK, frB] at *
        omega)
      (in_fr hp h.wr (by simp only [fK, frB]; omega)) fun t₁ m₁ => ?_
    have F₁ : Frame [sR s₀ fK 160] s.mem t₁.mem := by
      rw [m₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains s₀.sp (d := fK + 8 * j) (n := 8) (e := fK) (k := 160) (by omega) (by simp only [fK]; omega)
          (by simp only [fK]; omega))
    have k₁ : KR P s₀ t₁ := h.keep m₁.rd m₁.wr m₁.sp (fun r _ => by rw [m₁.gpr]) F₁
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj (.inl (by decide)) (by decide) (by decide))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub (by decide)⟩)
    exact stores_ok hp l (fun j' hj' => hl j' (by simp [hj'])) k₁ fun t h' g f =>
      k t h' (g.trans m₁.gpr) (F₁.trans f |>.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr; exact ⟨_, by simp, fun x hx => hx⟩)

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- The frame's body: our caller's registers restored, and the result. -/
theorem main_ok : WP isa P.c.main s₀ fun u => (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧
      u.gpr .ra = s₀.gpr .ra ∧ u.sp = s₀.sp ∧ u.wr = s₀.wr ∧ ∃ i, i < P.c.tries ∧
      (∀ j < i, sigI P s₀ j = none) ∧ (sigI P s₀ i ≠ none ∨ i + 1 = P.c.tries) ∧
      ResultIs s₀ (sigI P s₀ i) u := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.main
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (reduce_ok hp h₁) fun s₂ ⟨h₂, hh₂, _⟩ => ?_)
  refine WP.seq (WP.mono (initKV_ok hp h₂ hh₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (rekeyFull_ok hp h₃ (b := 0) (by decide)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (rekeyFull_ok hp h₄ (b := 1) (by decide)) fun s₅ h₅ => ?_)
  refine WP.seq ?_
  unfold Cfg.initCnt
  refine wp_li (imm := P.c.tries) P.hT' fun s₆ u₆ => WP.block_nil ?_
  have L₆ : LoopInv P s₀ 0 s₆ := by
    have e := kv0_eq P s₀
    refine ⟨P.hT, ⟨h₅.kr.upd (by decide) u₆, ?_, ?_, ?_⟩, by rw [u₆.gpr, Nat.sub_zero], fun j hj => absurd hj (by omega)⟩
    · rw [u₆.mem, h₅.k]; show _ = (kv0 P s₀).1; rw [e]
    · rw [u₆.mem, h₅.v]; show _ = (kv0 P s₀).2; rw [e]
    · rw [u₆.mem]; exact h₅.h
  refine WP.seq (WP.mono (loop_ok hp L₆) fun s₇ ⟨i, x₇⟩ => ?_)
  rw [Cfg.wipe, List.cons_append]
  refine wp_li (imm := 0) (by decide) fun s₈ u₈ => ?_
  refine stores_ok hp (List.range 20) (fun j hj => List.mem_range.mp hj) (x₇.kr.upd (by decide) u₈)
    fun s₉ k₉ g₉ f₉ => ?_
  refine WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp.al]) k₉.s1
    (by decide) restorable
    (fun q hq => in_fr' hp k₉.wr (by
      simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [frB] <;> omega))
    (k₉.saved.sub (by decide))) fun u hr => ⟨fun r hr' => ?_, ?_, by rw [hr.sp, k₉.sp], by rw [hr.wr, k₉.wr],
      i, x₇.lt, x₇.fails, x₇.last, ?_⟩
  · refine hr.gpr_of ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [.inl (by decide), .inl (by decide), .inl (by decide), .inl (by decide), .inl (by decide),
      .inl (by decide), .inr (k₉.nv _ (by simp)), .inr (k₉.nv _ (by simp)), .inr (k₉.nv _ (by simp)),
      .inr (k₉.nv _ (by simp)), .inr (k₉.nv _ (by simp)), .inr (k₉.nv _ (by simp))]
  · exact hr.gpr_of (.inl (by decide))
  · refine x₇.res.keep ?_ ?_
    · rw [hr.other _ (by decide), g₉, u₈.other _ (by decide)]
    · rw [hr.mem, fbytes f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.f_o.sub_left (part_sub (by decide))).symm) (by omega), u₈.mem]

end

/-! ## The frame -/

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hp : (rfcR P.I P.N).pre s) : Pre P (allocd frB s) := by
  have hz := sizes P
  have hX := hz.X
  have hlen : P.I.ecdsa.curve.len = 32 := by rw [P.hE]; rfl
  simp only [rfcR, hlen, P.hD] at hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hp
  have hN : P.N = frB + P.X := rfl
  have hspN : (s.sp - BitVec.ofNat 64 frB).toNat = s.sp.toNat - frB :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by rw [hN] at h9; omega) (by decide)
  have subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 frB, frB⟩ (below s.sp P.N) :=
    Offset.sub_below s.sp (by rw [hN]; omega) (by rw [hN]; omega)
  have subS : Region.Sub (below (s.sp - BitVec.ofNat 64 frB) P.X) (below s.sp P.N) := by
    have := below_body' s.sp frB P.X
    rwa [Nat.add_comm P.X, ← hN] at this
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, h10.sub_left subF, h11.sub_left subF, h12.sub_left subF, h13.sub_left subF,
    h10.sub_left subS, h11.sub_left subS, h12.sub_left subS, h13.sub_left subS, ?_, ?_, ?_, h14, h15, h16, h17, h18⟩
  · show (⟨s.sp - BitVec.ofNat 64 frB, frB⟩ : Region) :: s.wr = _
    rw [h2]; rfl
  · show (s.sp - BitVec.ofNat 64 frB).toNat % 16 = 0
    rw [hspN]; simp only [frB]; omega
  · show P.X ≤ (s.sp - BitVec.ofNat 64 frB).toNat
    rw [hspN]; rw [hN] at h9; omega
  · show (s.sp - BitVec.ofNat 64 frB).toNat + frB ≤ 2 ^ 64
    rw [hspN]; have := s.sp.isLt; rw [hN] at h9; omega

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold (s₀ : State) :
    result P.I s₀.mem (dk s₀) (dg s₀) =
      if 1 ≤ xOf s₀ ∧ xOf s₀ < Spec.P256.curve.n then
        Spec.Ecdsa.Rfc6979.search Spec.P256.curve P.hH.SH.H P.c.H.D (xOf s₀) (eOf P s₀) (kv0 P s₀).1 (kv0 P s₀).2
          P.c.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.sign, P.hct]
  rw [P.hE, P.hHash, P.hD]
  rfl

/-- Each candidate is one `V`. -/
theorem blocks_one (P : Rfc) : Spec.Ecdsa.Rfc6979.blocks Spec.P256.curve P.c.H.D = 1 := by
  have hz := sizes P
  obtain ⟨hD1, hD2⟩ := hz.D
  rw [Spec.Ecdsa.Rfc6979.blocks, VG.Proof.Ecdsa.Rfc6979.nBits_p256]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq (s₀ : State) {i : Nat} (hi : i < P.c.tries) (hf : ∀ j < i, sigI P s₀ j = none)
    (hl : sigI P s₀ i ≠ none ∨ i + 1 = P.c.tries) :
    (result P.I s₀.mem (dk s₀) (dg s₀)).1 = sigI P s₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf s₀ ∧ xOf s₀ < Spec.P256.curve.n
  · simp only [hv, and_self, ite_true]
    rw [VG.Proof.Ecdsa.Rfc6979.search_shift (blocks_one P) i P.c.tries (by omega) hf,
      show P.c.tries - i = (P.c.tries - 1 - i) + 1 by omega]
    cases hs : sigI P s₀ i with
    | some rs => rw [VG.Proof.Ecdsa.Rfc6979.search_ok (blocks_one P) hs]
    | none =>
      have h7 : i + 1 = P.c.tries := hl.resolve_left (by simp [hs])
      rw [VG.Proof.Ecdsa.Rfc6979.search_fail (blocks_one P) hs, show P.c.tries - 1 - i = 0 by omega]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-- The function, in its frame. -/
theorem correct {s : State} (hp : (rfcR P.I P.N).pre s) :
    WP isa P.c.sign s fun s' => abiPreserved s s' ∧ (rfcR P.I P.N).post s s' := by
  have hz := sizes P
  have hsp : P.N ≤ s.sp.toNat := hp.2.2.2.2.2.2.2.2.1
  have p := pre_alloc hp
  unfold Cfg.sign
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have : frB ≤ P.N := Nat.le_add_right _ _; omega)
    (WP.mono (main_ok p) fun s' ⟨hk, hra, hsp', hwr, i, hi, hf, hl, hres⟩ => ?_)
  rw [freed_eq hwr hsp']
  refine ⟨⟨fun r hr => hk r hr, rfl, hra⟩, ?_⟩
  have hlen : P.I.ecdsa.curve.len = 32 := by rw [P.hE]; rfl
  have hr := result_eq (s₀ := allocd frB s) hi hf hl
  show match (result P.I s.mem (s.gpr .a1) (s.gpr .a2)).1 with
    | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * P.I.ecdsa.curve.len) = Spec.Ecdsa.encode P.I.ecdsa.curve rs
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * P.I.ecdsa.curve.len) = List.replicate (2 * P.I.ecdsa.curve.len) 0
  rw [show s.mem = (allocd frB s).mem from rfl, show s.gpr = (allocd frB s).gpr from rfl, hr, hlen, P.hE]
  unfold ResultIs at hres
  split at hres <;> exact ⟨by rw [hres.1]; rfl, hres.2⟩

end VG.Proof.Ecdsa.Rfc6979.RISCV64
