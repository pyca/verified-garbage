module

-- separate module: its proofs (about 4 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.Num4
import VerifiedGarbage.Proof.Ecdh.RISCV64.Num0
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

One HMAC, `HMAC_K(parts)` (`Cfg.hmac`), for the key `K` at the frame's `K`
and a message in parts, each in the frame after the save area or the
private key `d` (`PartOk`), written to the frame at `dst`: HMAC's `init`
with `K` (`initArgs_ok`, `init_ok`), the streaming `update` on the inner
state with each part (`updArgs_ok`, `updc_ok`, `upds_ok`), and HMAC's
`finalize` (`finArgs_ok`, `fin_ok`). Until `finalize`, memory changes only
in the states (in `scratch`) and the stack below the frame (`St`), so the
key and the parts are those at the start; `hmac_ok` composes the pieces,
which the proof of constant time relates one by one.

The function, from the start of the frame's body: the prologue saves our
caller's `ra` and `s0`–`s5` and moves the pointers into `s0`–`s4` (`prologue_ok`, after which
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
    [mov .s1 .t0, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s0 .a4, mov .s6 .a5]) := rfl

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
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun q hq => by
      rw [t0, u₁.wr]
      exact in_fr hp rfl (by have := saved_in q hq; have := (sizes P).Q; have := (sizes P).H; omega)) ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => WP.block_nil ?_
  have mm : s₇.mem = Spill.saveMem s₁.mem s₀.sp s₁.gpr saved := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    show Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr saved = _
    rw [t0]
  have gg : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s0, .s6] → s₇.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g⟩ := hr
    exact (u₇.other r g).trans ((u₆.other r f).trans ((u₅.other r d).trans ((u₄.other r c).trans
      ((u₃.other r b).trans (u₂.other r a)))))
  have sv : Spill.Saved s₀.sp s₀.gpr saved s₇.mem := by
    rw [mm]
    intro q hq
    rw [Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact e₁ _ (by decide)
  refine ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd,
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr,
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_, sv, ?_⟩
  · upd_simp [u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr,
      u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr,
      u₂.other]
    exact t0
  · upd_simp [u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr,
      u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr,
      u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr,
      u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr,
      u₂.other]
    exact e₁ _ (by decide)
  · rw [gg q (by revert q; decide), e₁ q (by revert q hq; decide)]
  · rw [mm, u₁.mem]
    refine ((Spill.saveMem_frame_base (n := 64) (fun p hp' => (saved_in p hp').2) (by omega) _ _ _).sub
      fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR P s₀, by simp, Region.sub_prefix (by have := (sizes P).Q; have := (sizes P).H; omega)⟩

end

/-! ## `h = bits2octets(digest)` -/

/-- The values of the run: the private key and its bytes, the digest and its
integer, and `h`. -/
abbrev dB (P : Rfc) (s₀ : State) : List Byte := bytesAt s₀.mem (dk s₀) P.Q
abbrev xOf (P : Rfc) (s₀ : State) : Nat := Spec.Weierstrass.ofBytes (dB P s₀)
abbrev hBOf (P : Rfc) (s₀ : State) : List Byte := bytesAt s₀.mem (dg s₀) P.c.D
abbrev eOf (P : Rfc) (s₀ : State) : Nat := Spec.Ecdsa.hashToInt P.kit.E.curve (hBOf P s₀)
abbrev hSpec (P : Rfc) (s₀ : State) : List Byte := Spec.Ecdsa.Rfc6979.bits2octets P.kit.E.curve (hBOf P s₀)

/-- `V` and `h` in the frame. -/
abbrev vOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fV) P.c.D
abbrev hOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ P.c.fH) P.Q

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

/-- `loadQ`: the `Q` bytes at `p + off`, big-endian, to the slot at `o`, in
`nw` words. -/
theorem loadQ_ok (c : Cfg) (hQw : c.Q = 8 * c.nw ∨ (c.nw = 4 ∧ c.Q = 28) ∨ (c.nw = 4 ∧ c.Q = 24)) {s : State} {base : Addr} {o : Nat}
    {p : Reg} {off n : Nat} (hw : WsReg s base) (hp : p ∉ [Reg.t0, .t1]) (ho : o % 8 = 0)
    (ho' : o + 8 * c.nw ≤ 2048) (hoff : off + 8 * c.nw ≤ 2048)
    (hr : (⟨s.gpr p, n⟩ : Region) ∈ s.rd ++ s.wr) (hn : off + c.Q ≤ n) (hn' : n ≤ 8192)
    (hsep : ∀ i < c.Q, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (c.loadQ o p off)) s fun s' =>
      VG.Proof.X25519.RISCV64.Rest [.t0, .t1] s s' ∧ Outside base o (8 * c.nw) s.mem s'.mem ∧
      wordsVal s'.mem base o c.nw = Spec.Weierstrass.ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) c.Q) := by
  rcases hQw with h | ⟨h4, h28⟩ | ⟨h4, h24⟩
  · rw [Cfg.loadQ, ite_eq_left_of_eq_true _ _ (eq_true h), h]
    exact VG.Proof.Weierstrass.RISCV64.loadNum_ok c.nw hw hp ho (Nat.le_trans ho' (by decide)) hoff
      (fun j hj => Proof.Ecdh.RISCV64.P256.in_rd8 hr (by omega) hn') (fun i hi => hsep i (by omega))
  · rw [Cfg.loadQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h4, h28]
    exact VG.Proof.Weierstrass.RISCV64.loadNum4_ok 3 hw hp ho (by omega) (by omega)
      (VG.Proof.Weierstrass.RISCV64.in_rd4 hr (by omega) hn')
      (fun j hj => Proof.Ecdh.RISCV64.P256.in_rd8 hr (by omega) hn') (fun i hi => hsep i (by omega))
  · rw [Cfg.loadQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h4, h24]
    exact VG.Proof.Weierstrass.RISCV64.loadNum0_ok 3 hw hp ho (by omega) (by omega)
      (fun j hj => Proof.Ecdh.RISCV64.P256.in_rd8 hr (by omega) hn') (fun i hi => hsep i (by omega))

/-- `storeQ`: the `nw`-word number at `a` under the mask, to `q + off`
big-endian in `Q` bytes. -/
theorem storeQ_ok (c : Cfg) (hQw : c.Q = 8 * c.nw ∨ (c.nw = 4 ∧ c.Q = 28) ∨ (c.nw = 4 ∧ c.Q = 24)) (b : Bool) {s : State} {base : Addr}
    {a : Nat} {q : Reg} {off : Nat} (hw : WsReg s base) (hc : s.gpr .a7 = VG.Proof.Weierstrass.RISCV64.maskOf b)
    (hq : q ∉ [Reg.t0, .t1]) (ha : a % 8 = 0) (ha' : a + 8 * c.nw ≤ 2048) (hoff : off + 8 * c.nw ≤ 2048)
    (hout : ∀ i < c.Q, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + i)) 1)
    (hsep : ∀ i < c.Q, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (c.storeQ a q off)) s fun s' =>
      VG.Proof.X25519.RISCV64.Rest [.t0, .t1] s s' ∧ s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (Spec.Weierstrass.toBytes c.Q (if b then wordsVal s.mem base a c.nw else 0)) := by
  rcases hQw with h | ⟨h4, h28⟩ | ⟨h4, h24⟩
  · rw [Cfg.storeQ, ite_eq_left_of_eq_true _ _ (eq_true h), h]
    exact VG.Proof.Weierstrass.RISCV64.storeNum_ok b c.nw hw hc hq ha (Nat.le_trans ha' (by decide)) hoff
      (fun i hi => hout i (by omega)) (fun i hi => hsep i (by omega))
  · rw [Cfg.storeQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h4, h28]
    exact VG.Proof.Weierstrass.RISCV64.storeNum4_ok b 3 hw hc hq ha (by omega) (by omega)
      (fun i hi => hout i (by omega)) (fun i hi => hsep i (by omega))
  · rw [Cfg.storeQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h4, h24]
    exact VG.Proof.Weierstrass.RISCV64.storeNum_low_ok b 3 hw hc hq ha (by omega) (by omega)
      (fun i hi => hout i (by omega)) (fun i hi => hsep i (by omega))

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
      exact hp.f_c.sub_left (part_sub (by have := (sizes P).Q; have := (sizes P).H; omega)))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun x hx => hx⟩)

/-- The digest's leftmost `Q` bytes, the bytes apart from the working space. -/
theorem dg_out (hwd : P.c.wide = false) {i : Nat} (hi : i < P.Q) :
    ¬ (⟨scr s₀, 8192⟩ : Region).Contains (dg s₀ + BitVec.ofNat 64 (0 + i)) 1 :=
  Proof.Ecdh.RISCV64.P256.out_of_disj (n := P.Q)
    (hp.g_c.sub_left (Region.sub_prefix (by have := (sizes P).W.mp hwd; omega)))
    (by have := hp.ng; have := (sizes P).W.mp hwd; omega) (by omega)

theorem reduce_ok (hwd : P.c.wide = false) {s : State} (h : KR P s₀ s) :
    WP isa P.c.reduce s fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ ∧
      Frame [scrR s₀, sR s₀ P.c.fH P.Q] s.mem t.mem := by
  have hz := sizes P
  have hzH := hz.H
  have hn := P.kit.nw9
  have hQD : P.Q ≤ P.c.D := hz.W.mp hwd
  have hQw : P.c.Q = 8 * P.c.nw ∨ (P.c.nw = 4 ∧ P.c.Q = 28) ∨ (P.c.nw = 4 ∧ P.c.Q = 24) := by
    rw [P.hQ, P.hnw]
    rcases P.kit.Qw with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · have := hz.D; simp only [Rfc.Q] at hQD; omega
  have hzQ := hz.Q
  have := hz.H
  have hQQ : P.Q = P.kit.Q := rfl
  have hzD := hz.D
  have hw := ws_of hp h
  have hk := P.kit.FNk
  have hown : 4096 - 64 * P.kit.nw ≤ VG.Proof.Weierstrass.RISCV64.own P.kit.nw ∧
      VG.Proof.Weierstrass.RISCV64.own P.kit.nw + 64 * P.kit.nw ≤ 8192 := by
    rcases VG.Proof.Weierstrass.RISCV64.rvOwn_cases P.kit.nw with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
      rw [show VG.Proof.Weierstrass.RISCV64.own P.kit.nw = VG.Proof.Weierstrass.RISCV64.rvOwn P.kit.nw from rfl, h] <;>
      omega
  unfold Cfg.reduce
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hwd]; decide))]
  rw [P.hFN]
  simp only [Cfg.sZ, Cfg.sY]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadQ_ok P.c hQw hw (o := sX) (p := .s4) (off := 0) (n := P.c.D) (by decide)
    (by decide) (by simp only [sX, P.hnw]; omega) (by rw [P.hnw]; omega)
    (by rw [h.s4]; exact List.mem_append_left _ (by rw [h.rd, hp.rd]; simp))
    (by rw [P.hQ]; simp only [Rfc.Q] at hQD; omega) (by have := hz.D; omega)
    (fun i hi => by rw [h.s4]; exact dg_out hp hwd (by rw [P.hQ] at hi; exact hi))) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_
  simp only [P.hnw, P.hQ] at O₁ e₁
  rw [P.hnw]
  have hw₁ := hw.of_rest r₁
  refine WP.mono (VG.Proof.Weierstrass.RISCV64.setConst_ok P.kit.nw hw₁ (o := 8 * P.kit.nw) (x := 0) (by omega)
    (by omega)) fun s₂ ⟨r₂, O₂, e₂⟩ => ?_
  have hw₂ := hw₁.of_rest r₂
  have x₂ : wordsVal s₂.mem (scr s₀) sX P.kit.nw = Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) P.Q) := by
    rw [O₂.unch.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; simp only [sX]; omega)
      (by simp only [sX]; omega), e₁, h.s4, BitVec.add_zero]
    exact congrArg _ (h.dgBytes hp (n := P.Q) hQD)
  have hx : Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) P.Q) < 2 ^ (8 * P.kit.Q) := by
    have := VG.Proof.Ecdsa.Rfc6979.ofBytes_lt (bytesAt s₀.mem (dg s₀) P.Q)
    rwa [bytesAt_length] at this
  have two := P.kit.two (P.hsh hwd)
  rw [← P.kit.FNm] at two
  refine WP.seq (WP.mono (addCall_ok P.kit.FNok hw₂ (o := 2 * (8 * P.kit.nw)) (a := sX) (b := 8 * P.kit.nw)
    (by rw [hk]; omega) (by rw [hk]; simp only [sX]; omega) (by rw [hk]; omega)
    (by omega) (by simp only [sX]; omega) (by omega)
    (by
      rw [hk, x₂, e₂]
      simp only [Nat.zero_mod, Nat.add_zero]; omega)) fun s₃ ⟨C₃, v₃⟩ => ?_)
  rw [hk] at C₃ v₃
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
  have U₄ : Unch (scr s₀) ([(sX, 8 * P.kit.nw)] ++ [(8 * P.kit.nw, 8 * P.kit.nw)] ++
      [(2 * (8 * P.kit.nw), 8 * P.kit.nw), (VG.Proof.Weierstrass.RISCV64.own P.kit.nw, 64 * P.kit.nw)]) s.mem s₄.mem := by
    rw [u₄.mem]
    exact (O₁.unch.trans O₂.unch).trans C₃.mem
  have F₄ : Frame [scrR s₀] s.mem s₄.mem := frame_of_unch U₄ (by
    intro w hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp only [sX] <;> omega)
  have K₄ : KR P s₀ s₄ := KR.scr hp h rd₄ wr₄ sp₄ g₄ F₄
  have q₄ : s₄.gpr .s1 = s₀.sp := K₄.s1
  refine WP.mono (storeQ_ok P.c hQw true hw₄ a7 (q := .s1) (a := 2 * (8 * P.kit.nw))
    (off := P.c.fH) (by decide) (by omega) (by rw [P.hnw]; omega) (by rw [P.hnw]; have := (sizes P).H; have := (sizes P).Q; omega)
    (fun i hi => by rw [q₄]; exact in_fr hp K₄.wr (o := P.c.fH + i) (n := 1) (by rw [P.hQ] at hi; have := (sizes P).H; have := (sizes P).Q; omega))
    (fun i hi => by
      rw [q₄]
      refine Proof.Ecdh.RISCV64.P256.out_of_disj (n := P.c.frB) hp.f_c (by have := hp.top; omega)
        (by rw [P.hQ] at hi; have := (sizes P).H; have := (sizes P).Q; omega))) fun s₅ ⟨r₅, m₅⟩ => ?_
  rw [P.hnw, P.hQ] at m₅
  have v₄ : wordsVal s₄.mem (scr s₀) (2 * (8 * P.kit.nw)) P.kit.nw =
      Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) P.Q) % P.kit.E.curve.n := by
    rw [u₄.mem, v₃, x₂, e₂, P.kit.FNm]
    simp only [Nat.zero_mod, Nat.add_zero]
  have F₅ : Frame [sR s₀ P.c.fH P.Q] s₄.mem s₅.mem := by
    rw [m₅, q₄]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.Weierstrass.length_toBytes]; exact Region.contains_self _ _)
  refine ⟨K₄.keep r₅.rd r₅.wr r₅.sp (fun r hr => r₅.gpr r (by revert r; decide)) F₅
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega)) (by decide) (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, part_sub (P := P) (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega)⟩), ?_, ?_⟩
  · simp only [m₅, q₄, ↓reduceIte, v₄]
    have e := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₄.mem (sA s₀ P.c.fH)
      (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (bytesAt s₀.mem (dg s₀) P.Q) % P.kit.E.curve.n))
      (by rw [VG.Proof.Weierstrass.length_toBytes]; omega)
    rw [VG.Proof.Weierstrass.length_toBytes] at e
    show bytesAt _ (s₀.sp + BitVec.ofNat 64 P.c.fH) P.Q = _
    rw [e, hSpec, VG.Proof.Ecdsa.Rfc6979.bits2octets_eqQ (Q := P.Q) (P.nbits0 hwd)
      (by rw [bytesAt_length]; exact hQD)]
    rw [← bytesAt_take _ _ hQD]
  · refine (F₄.sub fun r hr => ?_).trans (F₅.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun x hx => hx⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨sR s₀ P.c.fH P.Q, by simp, fun x hx => hx⟩

end

/-- Bytes apart from what changed. -/
theorem fbytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

/-! ## Bytes stored in the frame -/

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- `storeBytes` of the bytes `bs` (each below 256) to the frame at `doff`,
after the save area. -/
theorem store_ok {s : State} (h : KR P s₀ s) {doff : Nat} {bs : List Nat} (hb : ∀ i < bs.length, bs.getD i 0 < 256)
    (hd : 64 ≤ doff ∧ doff + bs.length ≤ P.c.frB) :
    WP isa (.block (Impl.Words.RISCV64.storeBytes .t0 .s1 doff bs)) s fun t => KR P s₀ t ∧
      bytesAt t.mem (sA s₀ doff) bs.length = bs.map (BitVec.ofNat 8) ∧ Frame [sR s₀ doff bs.length] s.mem t.mem ∧
      ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hfr := (sizes P).Q
  have := (sizes P).H
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

/-- `copyBytes` of the `n` bytes at `soff(src)` to the frame at `doff`, after
the save area. -/
theorem copyFr_ok {s : State} (h : KR P s₀ s) {src : Reg} (hs0 : src ≠ .t0) {soff doff n : Nat}
    (hso : soff + n ≤ 2048) (hd : 64 ≤ doff ∧ doff + n ≤ P.c.frB)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (soff + i)) 1)
    (hsep : ∀ i < n, ¬ (sR s₀ doff n).Contains (s.gpr src + BitVec.ofNat 64 (soff + i)) 1) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 src .s1 soff doff n)) s fun t => KR P s₀ t ∧
      bytesAt t.mem (sA s₀ doff) n = bytesAt s.mem (s.gpr src + BitVec.ofNat 64 soff) n ∧
      Frame [sR s₀ doff n] s.mem t.mem ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hfr := (sizes P).Q
  have := (sizes P).H
  have e : s.gpr .s1 + BitVec.ofNat 64 doff = sA s₀ doff := by rw [h.s1]
  refine WP.mono (VG.RISCV64.Bytes.copyBytes_ok (s := s) (tmp := .t0) (src := src) (dst := .s1) (soff := soff)
    (doff := doff) (n := n) (Ne.symm hs0) (by decide) hso (by omega) hr
    (fun i hi => by rw [h.s1]; exact in_fr hp h.wr (o := doff + i) (n := 1) (by omega))
    (fun i hi => by rw [e]; exact hsep i hi)) fun t ht => ?_
  have F : Frame [sR s₀ doff n] s.mem t.mem := by have := ht.frame; rwa [e] at this
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
    rw [← e, add_ofNat_add'], ht.copied i (by simpa [bytesAt] using h₁), add_ofNat_add']

/-- If `wide`: `h`, the digest after `Q - D` zero bytes, which is
`bits2octets` of the digest. -/
theorem reduceW_ok (hwd : P.c.wide = true) {s : State} (h : KR P s₀ s) :
    WP isa P.c.reduce s fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ ∧
      Frame [sR s₀ P.c.fH P.Q] s.mem t.mem := by
  have hz := sizes P
  have hzH := hz.H
  have hzQ := hz.Q
  obtain ⟨hD1, hD2⟩ := hz.D
  have hQD : P.c.D < P.Q := by
    have := hz.W
    rw [hwd] at this
    simp only [Bool.true_eq_false, false_iff, Nat.not_le] at this
    exact this
  have hcQ : P.c.Q = P.Q := P.hQ
  have hnb : Spec.Ecdsa.nBits P.kit.E.curve + P.kit.sh = 8 * P.Q := P.kit.nbits
  have hsh := P.kit.sh8
  have hn0 : P.kit.E.curve.n ≠ 0 := fun h0 => by
    have := P.kit.nbits
    have := P.kit.sh8
    simp only [Spec.Ecdsa.nBits, h0, Nat.log2_zero] at *
    simp only [Rfc.Q] at hzQ
    omega
  unfold Cfg.reduce
  rw [ite_eq_left_of_eq_true _ _ (eq_true hwd), Cfg.reduceW, WP.block_append_iff, hcQ]
  refine WP.mono (store_ok hp h (doff := P.c.fH) (bs := List.replicate (P.Q - P.c.D) 0)
    (fun i hi => by simp only [List.length_replicate] at hi; simp [hi])
    (by simp only [List.length_replicate]; omega)) fun t₁ ⟨k₁, b₁, f₁, _⟩ => ?_
  refine WP.mono (copyFr_ok hp k₁ (src := .s4) (by decide) (soff := 0) (doff := P.c.fH + (P.Q - P.c.D))
    (n := P.c.D) (by omega) ⟨by omega, by omega⟩
    (fun i hi => by
      rw [k₁.s4]
      exact ⟨dgR P s₀, List.mem_append_left _ (by rw [k₁.rd, hp.rd]; simp),
        Offset.contains_base _ (by omega) (by have := hp.ng; omega)⟩)
    (fun i hi => by
      rw [k₁.s4]
      exact (hp.f_g.sub_left (part_sub (by omega))).symm _
        (Offset.contains_base _ (by omega) (by have := hp.ng; omega)))) fun t₂ ⟨k₂, b₂, f₂, _⟩ => ?_
  refine ⟨k₂, ?_, ?_⟩
  · have hl : P.Q = (P.Q - P.c.D) + P.c.D := by omega
    show bytesAt t₂.mem (sA s₀ P.c.fH) P.Q = _
    rw [hl, VG.Proof.Hmac.Common.bytesAt_add, add_ofNat_add', b₂, k₁.s4, BitVec.add_zero,
      k₁.dgBytes hp (Nat.le_refl _)]
    rw [List.length_replicate] at b₁
    rw [fbytes f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj (.inl (Nat.le_refl _)) (by omega) (by omega)) (by omega), b₁, hSpec,
      VG.Proof.Ecdsa.Rfc6979.bits2octets_short (R := P.Q) (by omega) (by omega) (by rw [bytesAt_length]; omega)
        hn0, bytesAt_length]
    simp
  · refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sR s₀ P.c.fH P.Q, by simp, Offset.sub _ (Nat.le_refl _) (by simp only [List.length_replicate]; omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sR s₀ P.c.fH P.Q, by simp, Offset.sub _ (by omega) (by omega)⟩

/-- `h = bits2octets(digest)`, either way. -/
theorem reduceAny_ok {s : State} (h : KR P s₀ s) :
    WP isa P.c.reduce s fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ := by
  cases hwd : P.c.wide
  · exact WP.mono (reduce_ok hp hwd h) fun _ ⟨a, b, _⟩ => ⟨a, b⟩
  · exact WP.mono (reduceW_ok hp hwd h) fun _ ⟨a, b, _⟩ => ⟨a, b⟩

end

/-! ## Steps b–g and h.3 -/

/-- `KR`, with `K`, `V` and `h`. -/
structure KVH (P : Rfc) (s₀ : State) (K V : List Byte) (t : State) : Prop where
  kr : KR P s₀ t
  k : kOf P s₀ t.mem = K
  v : vOf P s₀ t.mem = V
  h : hOf P s₀ t.mem = hSpec P s₀

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- A part of the frame apart from what an HMAC writes, the MAC at `dst` but. -/
theorem hd_apart {o n dst : Nat} (h : o + n ≤ P.c.frB) (hd : o + n ≤ dst ∨ dst + P.c.D ≤ o) (hdst : dst + P.c.D ≤ P.c.frB) :
    ∀ r ∈ [stR s₀, sR s₀ dst P.c.D, stk P s₀], Region.Disjoint (sR s₀ o n) r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact fr_st hp h (fun x hx => hx)
  · exact part_disj hd (by have := (sizes P).Q; have := (sizes P).H; omega) (by have := (sizes P).Q; have := (sizes P).H; omega)
  · exact (f_s hp).sub_left (part_sub h)

theorem initKV_ok {s : State} (h : KR P s₀ s) (hh : hOf P s₀ s.mem = hSpec P s₀) :
    WP isa (.block P.c.initKV) s (KVH P s₀ (List.replicate P.c.D 0) (List.replicate P.c.D 1)) := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.initKV
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hp h (doff := fK) (bs := List.replicate P.c.D 0) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fK, List.length_replicate]; have := (sizes P).Q; have := (sizes P).H; omega)) fun t₁ ⟨k₁, b₁, f₁, _⟩ => ?_
  refine WP.mono (store_ok hp k₁ (doff := fV) (bs := List.replicate P.c.D 1) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fV, List.length_replicate]; have := (sizes P).Q; have := (sizes P).H; omega)) fun t₂ ⟨k₂, b₂, f₂, _⟩ => ?_
  simp only [List.length_replicate, List.map_replicate] at b₁ b₂ f₁ f₂
  have hn : P.c.D ≤ 2 ^ 64 := by omega
  refine ⟨k₂, ?_, b₂, ?_⟩
  · show bytesAt t₂.mem (sA s₀ fK) P.c.D = _
    rw [fbytes f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fK, fV]; omega)) (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega) (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega)) hn, b₁]
    rfl
  · show bytesAt t₂.mem (sA s₀ P.c.fH) P.Q = _
    rw [fbytes f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega)) (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega) (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega))
      (by omega),
      fbytes f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega)) (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega) (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega))
      (by omega)]
    exact hh

/-- The separator `b` after `V`: the first part of the messages. -/
theorem sep_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) {b : Nat} (hb : b < 256) :
    WP isa (.block (P.c.sep b)) s fun t => KVH P s₀ K V t ∧
      bytesAt t.mem (sA s₀ fV) (P.c.D + 1) = V ++ [BitVec.ofNat 8 b] ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.sep
  refine WP.mono (store_ok hp h.kr (doff := fV + P.c.D) (bs := [b]) (fun i hi => by
      simp only [List.length_singleton] at hi; obtain rfl : i = 0 := by omega
      simpa using hb)
    (by simp only [fV, List.length_singleton]; have := (sizes P).Q; have := (sizes P).H; omega)) fun t ⟨k, bt, f, pr⟩ => ?_
  simp only [List.length_singleton, List.map_cons, List.map_nil] at bt f
  have hv : vOf P s₀ t.mem = V := by
    rw [← h.v]
    exact fbytes f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by omega)) (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega) (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega)) (by omega)
  refine ⟨⟨k, ?_, hv, ?_⟩, ?_, pr⟩
  · rw [← h.k]
    exact fbytes f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fK, fV]; omega)) (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega) (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega))
      (by omega)
  · rw [← h.h]
    exact fbytes f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega)) (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega) (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega))
      (by omega)
  · rw [VG.Proof.Hmac.Common.bytesAt_add, show bytesAt t.mem (sA s₀ fV) P.c.D = V from hv]
    rw [show sA s₀ fV + BitVec.ofNat 64 P.c.D = sA s₀ (fV + P.c.D) from add_ofNat_add' _ _ _, bt]

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) (hsy : s.syms = s₀.syms) :
    WP isa P.c.hmacV s fun t => KVH P s₀ K (Spec.Hmac.hmac P.hH.SH.H K V) t ∧
      ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.hmacV
  refine WP.mono (hmac_ok hp h.kr hsy P.hD4 (ps := [(.s1, fV, P.c.D)]) (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := fV) ⟨by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩) fun t ⟨k, _, hv, f, pr⟩ => ?_
  have hm : msgOf s.mem s₀ [(.s1, fV, P.c.D)] = V := by
    simp only [msgOf, List.append_nil]; exact h.v
  refine ⟨⟨k, ?_, ?_, ?_⟩, pr⟩
  · rw [← h.k]
    exact fbytes f (hd_apart hp (by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega) (.inl (by simp only [fK, fV]; omega))
      (by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)
  · show bytesAt t.mem (sA s₀ fV) P.c.D = _
    rw [hv, hm, h.k]
  · rw [← h.h]
    exact fbytes f (hd_apart hp (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; have := (sizes P).Q; have := (sizes P).H; omega) (.inr (by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega))
      (by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) (hsy : s.syms = s₀.syms) {b : Nat} (hb : b < 256) :
    WP isa (P.c.rekeyFull b) s fun t =>
      let K' := Spec.Hmac.hmac P.hH.SH.H K (V ++ BitVec.ofNat 8 b :: (dB P s₀ ++ hSpec P s₀))
      KVH P s₀ K' (Spec.Hmac.hmac P.hH.SH.H K' V) t := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.rekeyFull
  rw [hz.Q.2.2.1]
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (sep_ok hp h hb) fun s₁ ⟨h₁, m₁, _⟩ y₁ => ?_)
  refine WP.seq (WP.mono (hmac_ok hp h₁.kr (y₁.trans hsy) P.hD4 (ps := [(.s1, fV, P.c.D + 1), (.s3, 0, P.Q), (.s1, P.c.fH, P.Q)])
    (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      · exact .inl ⟨rfl, by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩
      · exact .inr ⟨rfl, rfl, Nat.le_refl _⟩
      · exact .inl ⟨rfl, by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega, by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; have := (sizes P).Q; have := (sizes P).H; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := fK) ⟨by decide, by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega⟩) fun t ⟨k, y, hk, f, pr⟩ => ?_)
  have hm : msgOf s₁.mem s₀ [(.s1, fV, P.c.D + 1), (.s3, 0, P.Q), (.s1, P.c.fH, P.Q)] =
      V ++ BitVec.ofNat 8 b :: (dB P s₀ ++ hSpec P s₀) := by
    simp only [msgOf, List.append_nil, pA, regV]
    rw [m₁, BitVec.add_zero, h₁.kr.dBytes hp]
    have hh := h₁.h
    simp only [hOf] at hh
    rw [hh]
    simp
  refine WP.mono (hmacV_ok hp (K := Spec.Hmac.hmac P.hH.SH.H K (V ++ BitVec.ofNat 8 b :: (dB P s₀ ++ hSpec P s₀)))
    (V := V) ⟨k, ?_, ?_, ?_⟩ y) fun u hu => hu.1
  · show bytesAt t.mem (sA s₀ fK) P.c.D = _
    rw [hk, hm, h₁.k]
  · rw [← h₁.v]
    exact fbytes f (hd_apart hp (by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega) (.inr (by simp only [fK, fV]; omega))
      (by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)
  · rw [← h₁.h]
    exact fbytes f (hd_apart hp (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; have := (sizes P).Q; have := (sizes P).H; omega) (.inr (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega))
      (by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) (hsy : s.syms = s₀.syms) :
    WP isa P.c.rekey s (fun t => KVH P s₀ (Spec.Ecdsa.Rfc6979.next P.hH.SH.H K V).1
      (Spec.Ecdsa.Rfc6979.next P.hH.SH.H K V).2 t ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r) := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  unfold Cfg.rekey
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (sep_ok hp h (b := 0) (by decide)) fun s₁ ⟨h₁, m₁, pr₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono (hmac_ok hp h₁.kr (y₁.trans hsy) P.hD4 (ps := [(.s1, fV, P.c.D + 1)])
    (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := fK) ⟨by decide, by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega⟩) fun t ⟨k, y, hk, f, pr⟩ => ?_)
  refine WP.mono (hmacV_ok hp (K := Spec.Hmac.hmac P.hH.SH.H K (V ++ [0])) (V := V) ⟨k, ?_, ?_, ?_⟩ y)
    fun u hu => ⟨hu.1, fun r hr => (hu.2 r hr).trans ((pr r hr).trans (pr₁ r hr))⟩
  · show bytesAt t.mem (sA s₀ fK) P.c.D = _
    rw [hk]
    simp only [msgOf, List.append_nil, pA, regV]
    rw [m₁, h₁.k]
    rfl
  · rw [← h₁.v]
    exact fbytes f (hd_apart hp (by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega) (.inr (by simp only [fK, fV]; omega))
      (by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)
  · rw [← h₁.h]
    exact fbytes f (hd_apart hp (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; have := (sizes P).Q; have := (sizes P).H; omega) (.inr (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega))
      (by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)


/-- If `wide`, a candidate: `V₁ = HMAC_K(V)` to `fT`, `V₂ = HMAC_K(V₁)` to
`V`'s place, and the first `Q - D` bytes of `V₂` after `V₁`. -/
theorem candW_ok (hwd : P.c.wide = true) {s : State} {K V : List Byte} (h : KVH P s₀ K V s) (hsy : s.syms = s₀.syms) :
    WP isa P.c.candW s fun t =>
      KVH P s₀ K (Spec.Hmac.hmac P.hH.SH.H K (Spec.Hmac.hmac P.hH.SH.H K V)) t ∧
      bytesAt t.mem (sA s₀ P.c.fT) P.Q =
        (Spec.Hmac.hmac P.hH.SH.H K V ++ Spec.Hmac.hmac P.hH.SH.H K (Spec.Hmac.hmac P.hH.SH.H K V)).take P.Q ∧
      ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hz := sizes P
  have hzH := hz.H
  have hzQ := hz.Q
  obtain ⟨hD1, hD2⟩ := hz.D
  have hB := hz.B
  have hnu : P.c.nums = 2 := by rw [hz.nums, hwd]; rfl
  have hQD : P.c.D < P.Q := by
    have := hz.W
    rw [hwd] at this
    simp only [Bool.true_eq_false, false_iff, Nat.not_le] at this
    exact this
  have hfT : P.c.fT = P.c.fH + 8 * P.kit.nw := by rw [Cfg.fT, P.hnw]
  have hfr := hzQ.2.2.2.1.1
  rw [hnu] at hfr
  have hQ8 := hzQ.2.2.2.2.1
  have hcQ : P.c.Q = P.Q := P.hQ
  unfold Cfg.candW
  rw [hcQ]
  -- `V₁ = HMAC_K(V)` to `fT`.
  refine WP.seq (WP.mono (hmac_ok hp h.kr hsy P.hD4 (ps := [(.s1, fV, P.c.D)]) (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by (try dsimp only); simp only [fV]; omega, by (try dsimp only); simp only [fV]; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := P.c.fT) ⟨by omega, by omega⟩) fun t₁ ⟨k₁, y₁, v₁, f₁, pr₁⟩ => ?_)
  have hm₁ : msgOf s.mem s₀ [(.s1, fV, P.c.D)] = V := by simp only [msgOf, List.append_nil]; exact h.v
  rw [hm₁, h.k] at v₁
  have kk₁ : kOf P s₀ t₁.mem = K := by
    rw [← h.k]
    exact fbytes f₁ (hd_apart hp (by simp only [fK]; omega) (.inl (by simp only [fK]; omega)) (by omega)) (by omega)
  have hh₁ : hOf P s₀ t₁.mem = hSpec P s₀ := by
    rw [← h.h]
    exact fbytes f₁ (hd_apart hp (by omega) (.inl (by omega)) (by omega)) (by omega)
  -- `V₂ = HMAC_K(V₁)` to `V`'s place.
  refine WP.seq (WP.mono (hmac_ok hp k₁ y₁ P.hD4 (ps := [(.s1, P.c.fT, P.c.D)]) (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by (try dsimp only); omega, by (try dsimp only); omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega)
    (dst := fV) ⟨by simp only [fV]; omega, by simp only [fV]; omega⟩) fun t₂ ⟨k₂, _, v₂, f₂, pr₂⟩ => ?_)
  have hm₂ : msgOf t₁.mem s₀ [(.s1, P.c.fT, P.c.D)] = Spec.Hmac.hmac P.hH.SH.H K V := by
    simp only [msgOf, List.append_nil]; exact v₁
  rw [hm₂, kk₁] at v₂
  have kk₂ : kOf P s₀ t₂.mem = K := by
    rw [← kk₁]
    exact fbytes f₂ (hd_apart hp (by simp only [fK]; omega) (.inl (by simp only [fK, fV]; omega))
      (by simp only [fV]; omega)) (by omega)
  have hh₂ : hOf P s₀ t₂.mem = hSpec P s₀ := by
    rw [← hh₁]
    exact fbytes f₂ (hd_apart hp (by omega) (.inr (by simp only [fV]; omega)) (by simp only [fV]; omega)) (by omega)
  have T₂ : bytesAt t₂.mem (sA s₀ P.c.fT) P.c.D = Spec.Hmac.hmac P.hH.SH.H K V := by
    rw [← v₁]
    exact fbytes f₂ (hd_apart hp (by omega) (.inr (by simp only [fV]; omega)) (by simp only [fV]; omega)) (by omega)
  -- `V₂`'s first `Q - D` bytes after `V₁`.
  refine WP.mono (copyFr_ok hp k₂ (src := .s1) (by decide) (soff := fV) (doff := P.c.fT + P.c.D)
    (n := P.Q - P.c.D) (by simp only [fV]; omega) ⟨by omega, by omega⟩
    (fun i hi => by rw [k₂.s1]; exact in_fr' hp k₂.wr (o := fV + i) (n := 1) (by simp only [fV]; omega))
    (fun i hi => by
      rw [k₂.s1]
      exact part_disj (s₀ := s₀) (a := fV + i) (m := 1) (b := P.c.fT + P.c.D) (n := P.Q - P.c.D)
        (.inl (by simp only [fV]; omega)) (by simp only [fV]; omega) (by omega) _ (Region.contains_self _ _)))
    fun t₃ ⟨k₃, b₃, f₃, pr₃⟩ => ?_
  have ap : ∀ {o n : Nat}, o + n ≤ P.c.fT + P.c.D → ∀ r ∈ [sR s₀ (P.c.fT + P.c.D) (P.Q - P.c.D)],
      Region.Disjoint (sR s₀ o n) r := fun ho r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact part_disj (.inl ho) (by omega) (by omega)
  have hV₁ : (Spec.Hmac.hmac P.hH.SH.H K V).length = P.c.D := by rw [← T₂, bytesAt_length]
  refine ⟨⟨k₃, ?_, ?_, ?_⟩, ?_, fun r hr => (pr₃ r hr).trans ((pr₂ r hr).trans (pr₁ r hr))⟩
  · rw [← kk₂]; exact fbytes f₃ (ap (by simp only [fK]; omega)) (by omega)
  · show bytesAt t₃.mem (sA s₀ fV) P.c.D = _
    rw [fbytes f₃ (ap (by simp only [fV]; omega)) (by omega)]; exact v₂
  · rw [← hh₂]; exact fbytes f₃ (ap (by omega)) (by omega)
  · rw [show P.Q = P.c.D + (P.Q - P.c.D) by omega, VG.Proof.Hmac.Common.bytesAt_add, add_ofNat_add', b₃,
      k₂.s1, fbytes f₃ (ap (Nat.le_refl _)) (by omega), T₂, List.take_append, hV₁,
      List.take_of_length_le (by omega), Nat.add_sub_cancel_left, ← v₂, ← bytesAt_take _ _ (by omega)]

end

/-! ## The candidates -/

/-- `K` and `V` after steps b–g, before candidate `i`, candidate `i`'s `V`,
and its signature. -/
abbrev kv0 (P : Rfc) (s₀ : State) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.kit.E.curve P.hH.SH.H P.c.D (xOf P s₀) (hBOf P s₀)
/-- The `V`s a candidate takes. -/
def nb (P : Rfc) : Nat := Spec.Ecdsa.Rfc6979.blocks P.kit.E.curve P.c.D
abbrev kvI (P : Rfc) (s₀ : State) (i : Nat) : List Byte × List Byte :=
  VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H (nb P) (kv0 P s₀).1 (kv0 P s₀).2 i
abbrev candI (P : Rfc) (s₀ : State) (i : Nat) : List Byte :=
  VG.Proof.Ecdsa.Rfc6979.candAtB P.hH.SH.H (nb P) (kv0 P s₀).1 (kv0 P s₀).2 i
abbrev sigI (P : Rfc) (s₀ : State) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.kit.E.curve (xOf P s₀) (eOf P s₀) (Spec.Ecdsa.Rfc6979.bits2int P.kit.E.curve (candI P s₀ i))

/-- One `V`, or two if `wide`. -/
theorem nb_eq (P : Rfc) : nb P = if P.c.wide then 2 else 1 := by
  have hz := sizes P
  have hn := P.kit.nbits
  have h8 := P.kit.sh8
  have hD := hz.D
  have hQ := hz.Q
  rw [nb, Spec.Ecdsa.Rfc6979.blocks]
  have hQ' := hz.Q.2.2.1
  cases hwd : P.c.wide
  · have := hz.W.mp hwd
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [Rfc.Q] at *
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · have : ¬ P.Q ≤ P.c.D := fun h => by rw [hz.W.mpr h] at hwd; exact absurd hwd (by decide)
    simp only [↓reduceIte]
    simp only [Rfc.Q] at *
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- If not `wide`, a candidate is one `V`. -/
theorem genT_one (P : Rfc) (hwd : P.c.wide = false) (K V : List Byte) :
    Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K (nb P) V = (Spec.Hmac.hmac P.hH.SH.H K V ++ [], Spec.Hmac.hmac P.hH.SH.H K V) := by
  rw [nb_eq, hwd]; rfl

/-- If `wide`, a candidate is two `V`s. -/
theorem genT_two (P : Rfc) (hwd : P.c.wide = true) (K V : List Byte) :
    Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K (nb P) V =
      (Spec.Hmac.hmac P.hH.SH.H K V ++ (Spec.Hmac.hmac P.hH.SH.H K (Spec.Hmac.hmac P.hH.SH.H K V) ++ []),
        Spec.Hmac.hmac P.hH.SH.H K (Spec.Hmac.hmac P.hH.SH.H K V)) := by
  rw [nb_eq, hwd]; rfl

/-- Before candidate `i`. -/
structure LoopInv (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  kvh : KVH P s₀ (kvI P s₀ i).1 (kvI P s₀ i).2 t
  cnt : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)
  fails : ∀ j < i, sigI P s₀ j = none
  sy : t.syms = s₀.syms

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : Rfc) (s₀ : State) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => t.gpr .a0 = 1 ∧ bytesAt t.mem (out s₀) (2 * P.Q) = Spec.Ecdsa.encode P.kit.E.curve rs
  | none => t.gpr .a0 = 0 ∧ bytesAt t.mem (out s₀) (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  lt : i < P.c.tries
  kr : KR P s₀ t
  fails : ∀ j < i, sigI P s₀ j = none
  last : sigI P s₀ i ≠ none ∨ i + 1 = P.c.tries
  res : ResultIs P s₀ (sigI P s₀ i) t

theorem ResultIs.keep {P : Rfc} {s₀ : State} {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P s₀ r t)
    (ha : t'.gpr .a0 = t.gpr .a0) (hm : bytesAt t'.mem (out s₀) (2 * P.Q) = bytesAt t.mem (out s₀) (2 * P.Q)) :
    ResultIs P s₀ r t' := by
  unfold ResultIs at *
  split at h <;> exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- What `core` reads is candidate `i`'s signature's input. -/
theorem sg_eq (hwd : P.c.wide = false) {t : State} (hk : KR P s₀ t) {i : Nat}
    (hv : vOf P s₀ t.mem = Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2) :
    sgOf P.kit.E P.Q P.kit.G P.kit.sh t.mem (dk s₀) (dg s₀) (sA s₀ fV) = sigI P s₀ i := by
  have hz := sizes P
  have hzH := hz.H
  have hD1 : P.Q ≤ P.c.D := hz.W.mp hwd
  have hq : Spec.Ecdsa.nBits P.kit.E.curve = 8 * P.Q := P.nbits0 hwd
  have hc : candI P s₀ i = vOf P s₀ t.mem ++ [] := by
    rw [hv]; exact congrArg Prod.fst (genT_one P hwd _ _)
  rw [P.G0 hwd, P.hsh hwd]
  simp only [sgOf, sigI, Nat.shiftRight_zero]
  congr 1
  · exact congrArg _ (hk.dBytes hp)
  · rw [eOf, hk.dgBytes hp (n := P.Q) (by omega),
      VG.Proof.Ecdsa.Rfc6979.hashToInt_takeQ hq (by rw [bytesAt_length]),
      VG.Proof.Ecdsa.Rfc6979.hashToInt_takeQ hq (by rw [bytesAt_length]; omega), ← bytesAt_take _ _ hD1,
      List.take_of_length_le (by rw [bytesAt_length])]
  · rw [hc, Spec.Ecdsa.Rfc6979.bits2int, List.append_nil,
      VG.Proof.Ecdsa.Rfc6979.hashToInt_takeQ hq (by rw [bytesAt_length]; omega), ← bytesAt_take _ _ hD1]

/-- If `wide`: what `core` reads, the digest and the candidate's leftmost
`Q` bytes at `fT`, is candidate `i`'s signature's input. -/
theorem sg_eqW (hwd : P.c.wide = true) {t : State} (hk : KR P s₀ t) {i : Nat}
    (hT : bytesAt t.mem (sA s₀ P.c.fT) P.Q = (candI P s₀ i).take P.Q) (hl : P.Q ≤ (candI P s₀ i).length) :
    sgOf P.kit.E P.Q P.kit.G P.kit.sh t.mem (dk s₀) (dg s₀) (sA s₀ P.c.fT) = sigI P s₀ i := by
  have hq : Spec.Ecdsa.nBits P.kit.E.curve + P.kit.sh = 8 * P.Q := P.kit.nbits
  rw [P.GW hwd]
  simp only [sgOf, sigI]
  congr 1
  · exact congrArg _ (hk.dBytes hp)
  · rw [eOf, hk.dgBytes hp (n := P.c.D) (Nat.le_refl _)]
  · rw [Spec.Ecdsa.Rfc6979.bits2int, VG.Proof.Ecdsa.Rfc6979.hashToInt_takeR (R := P.Q) (by omega) hl, ← hT,
      show 8 * P.Q - Spec.Ecdsa.nBits P.kit.E.curve = P.kit.sh by omega]

/-- The tables are kept: the code writes only `wrs`. -/
theorem held_of {t : State} (hk : KR P s₀ t) : Abi.constsHeld t.mem (fun name => s₀.syms name) P.kit.K :=
  fun c hc i hi => by
  rw [← hp.held c hc i hi]
  have hr : (⟨s₀.syms c.1, 8 * c.2.length⟩ : Region) ∈ constRegs P.kit.K s₀ := List.mem_map_of_mem hc
  have := hp.tfit _ hr
  refine Mem.readW_congr fun b hb => hk.frame _ fun r hr' hc' => hp.t_w _ hr r hr' _ ?_ hc'
  simp only [Region.Contains] at this ⊢
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Mem.sub_ofNat_toNat _ (by omega)]
  omega

/-- `core`'s arguments, with `k` at `ko` in the frame. -/
theorem coreArgs_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) (hsy : t.syms = s₀.syms) {ko : Nat}
    (hko : 64 ≤ ko ∧ ko + P.Q ≤ P.c.frB) :
    WP isa (.block [mov .a0 .s2, mov .a1 .s3, mov .a2 .s4, .addi .a3 .s1 ko, mov .a4 .s0]) t fun u =>
      KVH P s₀ K V u ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧ u.mem = t.mem ∧
      CoreArgsG P.Q P.kit.G P.kit.K u (out s₀) (dk s₀) (dg s₀) (sA s₀ ko) (scr s₀) := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  have hGD : P.kit.G ≤ P.c.D := by
    rw [P.hG]; cases hwd : P.c.wide
    · exact hz.W.mp hwd
    · exact Nat.le_refl _
  have hko' : ko < 2048 := by have := (sizes P).Q; omega
  refine VG.Proof.Ecdsa.RISCV64.Comb.WP.of_syms (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    wp_addi hko' fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil fun sy₅ => ?_)
  have mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₅ : KR P s₀ s₅ := (((((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd
    (by decide) u₄).upd (by decide) u₅)
  have hQ := hz.Q
  have ef : (fun name => s₅.syms name) = fun name => s₀.syms name := by rw [sy₅, hsy]
  have cr : constRegs P.kit.K s₅ = constRegs P.kit.K s₀ := by simp only [constRegs, ef]
  have kS : Region.Sub ⟨sA s₀ ko, P.Q⟩ (frR P s₀) := part_sub hko.2
  have gS : Region.Sub ⟨dg s₀, P.kit.G⟩ (dgR P s₀) := Region.sub_prefix hGD
  have hk32 : (sA s₀ ko).toNat + P.Q ≤ 2 ^ 64 := by
    have := hp.top
    show (s₀.sp + BitVec.ofNat 64 ko).toNat + P.Q ≤ 2 ^ 64
    rw [VG.Offset.toNat_add_ofNat]; have := (sizes P).Q; have := (sizes P).H; omega
  refine ⟨⟨k₅, by rw [mm]; exact h.k, by rw [mm]; exact h.v, by rw [mm]; exact h.h⟩, fun r hr => ?_, mm, ?_, ?_, ?_, ?_, ?_,
    hp.o_c, hp.d_c, hp.g_c.sub_left gS, hp.f_c.sub_left kS, hp.no, hp.nd,
    by have := hp.ng; omega, hk32, hp.nc, hp.ca, by rw [mm, ef]; exact held_of hp h.kr,
    by rw [cr]; exact hp.tfit, by rw [cr]; exact hp.tal,
    fun r hr => hp.t_w r (by rwa [cr] at hr) _ (by simp),
    fun r hr => hp.t_w r (by rwa [cr] at hr) _ (by simp), ?_, ?_⟩
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
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (((rfl | rfl | rfl) | hr) | rfl | rfl)
    · exact ⟨dR P s₀, List.mem_append_left _ (by rw [k₅.rd, hp.rd]; simp), 0, by simp, by simp⟩
    · exact ⟨dgR P s₀, List.mem_append_left _ (by rw [k₅.rd, hp.rd]; simp), 0, by simp, by simp only; omega⟩
    · exact cov_fr hp k₅ (o := ko) (n := P.Q) hko.2
    · exact ⟨r, List.mem_append_left _ (by rw [k₅.rd, hp.rd, ← cr]; exact List.mem_append_right _ hr), 0,
        by simp, by simp⟩
    · exact ⟨outR P s₀, List.mem_append_right _ (out_wr hp k₅.wr), 0, by simp, by simp⟩
    · exact cov_scr hp k₅ (o := 0) (n := 8192) (by decide) |>.imp fun r' ⟨hm, off, hb, hl⟩ =>
        ⟨hm, off, by rw [← hb]; simp, hl⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨outR P s₀, out_wr hp k₅.wr, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, scr_wr hp k₅.wr, 0, by simp, by simp⟩

/-- `core` with candidate `i`. -/
theorem coreCall_ok {t : State} {K V : List Byte} (h : KVH P s₀ K V t) {i ko : Nat}
    (hsg : sgOf P.kit.E P.Q P.kit.G P.kit.sh t.mem (dk s₀) (dg s₀) (sA s₀ ko) = sigI P s₀ i)
    (ha : CoreArgsG P.Q P.kit.G P.kit.K t (out s₀) (dk s₀) (dg s₀) (sA s₀ ko) (scr s₀)) :
    WP isa (.call P.c.coreN P.c.coreC) t fun u => KVH P s₀ K V u ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      ResultIs P s₀ (sigI P s₀ i) u := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  rw [P.hcC]
  refine P.kit.core_call ha fun u a hpost => ?_
  have hw : ∀ r ∈ [(⟨out s₀, 2 * P.Q⟩ : Region), ⟨scr s₀, 8192⟩], Wk P s₀ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl fun x hx => hx)
    · exact .inr (.inr (.inl fun x hx => hx))
  have kp : ∀ {o n : Nat}, o + n ≤ P.c.frB → ∀ r ∈ [(⟨out s₀, 2 * P.Q⟩ : Region), ⟨scr s₀, 8192⟩],
      Region.Disjoint (sR s₀ o n) r := fun ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.f_o.sub_left (part_sub ho)
    · exact hp.f_c.sub_left (part_sub ho)
  refine ⟨⟨h.kr.call hp a.rd a.wr a.sp a.cs a.frame hw, ?_, ?_, ?_⟩, a.cs, ?_⟩
  · rw [← h.k]; exact fbytes a.frame (kp (by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)
  · rw [← h.v]; exact fbytes a.frame (kp (by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)
  · rw [← h.h]; exact fbytes a.frame (kp (by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; have := (sizes P).Q; have := (sizes P).H; omega)) (by omega)
  · rw [hsg] at hpost
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
    (hc : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)) (hr : ResultIs P s₀ (sigI P s₀ i) t) :
    WP isa (.block Cfg.goOn) t fun u => KVH P s₀ K V u ∧ ResultIs P s₀ (sigI P s₀ i) u ∧
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

/-- After `core`: whether to go on, and step h.3 or the end. -/
theorem tryRest_ok {t : State} {i : Nat} (hlt : i < P.c.tries) (hf : ∀ j < i, sigI P s₀ j = none)
    (k₃ : KVH P s₀ (kvI P s₀ i).1
      (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (kvI P s₀ i).1 (nb P) (kvI P s₀ i).2).2 t)
    (c₃ : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)) (r₃ : ResultIs P s₀ (sigI P s₀ i) t)
    (y₃ : t.syms = s₀.syms) :
    WP isa (.seq (.block Cfg.goOn) (.ite (.nonzero .t6) (.seq P.c.rekey (.block Cfg.again)) (.block Cfg.stop))) t
      fun u =>
      isa.eval (.nonzero .t6) u = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) ∧
      (sigI P s₀ i = none ∧ i + 1 < P.c.tries → LoopInv P s₀ (i + 1) u) ∧
      (¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) → Exit P s₀ i u) := by
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (goOn_ok k₃ hlt c₃ r₃) fun t₄ ⟨k₄, r₄, c₄, e₄⟩ y₄ => ?_)
  have y₄' : t₄.syms = s₀.syms := y₄.trans y₃
  refine WP.ite _ e₄ (fun hg => ?_) fun hg => ?_
  · obtain ⟨hn, hlt'⟩ := of_decide_eq_true hg
    refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (rekey_ok hp k₄ y₄') fun t₅ ⟨k₅, p₅⟩ y₅ => ?_)
    refine VG.Proof.Ecdsa.RISCV64.Comb.WP.of_syms (wp_li (imm := 1) (by decide) fun t₆ u₆ =>
      WP.block_nil fun y₆ => ⟨?_, fun _ => ?_, fun hn' => absurd ⟨hn, hlt'⟩ hn'⟩)
    · rw [VG.RISCV64.Steps.eval_nonzero, u₆.gpr, decide_eq_true ⟨hn, hlt'⟩]; rfl
    · have m₆ : t₆.mem = t₅.mem := u₆.mem
      refine ⟨hlt', ⟨k₅.kr.upd (by decide) u₆, by rw [m₆]; exact k₅.k, by rw [m₆]; exact k₅.v,
        by rw [m₆]; exact k₅.h⟩, ?_, fun j hj => ?_, y₆.trans (y₅.trans y₄')⟩
      · rw [u₆.other _ (by decide), p₅ _ (by decide), c₄]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hf j hj
        · exact hn
  · have hl : ¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) := of_decide_eq_false hg
    refine wp_li (imm := 0) (by decide) fun t₅ u₅ => WP.block_nil ⟨?_, fun h' => absurd h' hl, fun _ => ?_⟩
    · rw [VG.RISCV64.Steps.eval_nonzero, u₅.gpr, decide_eq_false hl]; rfl
    · refine ⟨hlt, k₄.kr.upd (by decide) u₅, hf, ?_, r₄.keep (u₅.other _ (by decide)) (by rw [u₅.mem])⟩
      by_cases hs : sigI P s₀ i = none
      · have h1 := hlt
        have h2 : ¬ i + 1 < P.c.tries := fun h' => hl ⟨hs, h'⟩
        exact .inr (by omega)
      · exact .inl hs

/-- One candidate: on, before the next, or the end. -/
theorem tryOne_ok {t : State} {i : Nat} (h : LoopInv P s₀ i t) :
    WP isa P.c.tryOne t fun u =>
      isa.eval (.nonzero .t6) u = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) ∧
      (sigI P s₀ i = none ∧ i + 1 < P.c.tries → LoopInv P s₀ (i + 1) u) ∧
      (¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) → Exit P s₀ i u) := by
  have hz := sizes P
  have hzQ := hz.Q
  have hzH := hz.H
  have hzD := hz.D
  unfold Cfg.tryOne
  cases hwd : P.c.wide
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    have hQD := hz.W.mp hwd
    refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (hmacV_ok hp h.kvh h.sy) fun t₁ ⟨k₁, p₁⟩ y₁ => ?_)
    refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreArgs_ok hp k₁ (y₁.trans h.sy) (ko := fV)
      ⟨by decide, by simp only [fV]; omega⟩) fun t₂ ⟨k₂, p₂, _, a₂⟩ y₂ => ?_)
    refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreCall_ok hp k₂ (sg_eq hp hwd k₂.kr k₂.v) a₂)
      fun t₃ ⟨k₃, p₃, r₃⟩ y₃ => ?_)
    have e : (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (kvI P s₀ i).1 (nb P) (kvI P s₀ i).2).2 =
        Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2 := congrArg Prod.snd (genT_one P hwd _ _)
    exact tryRest_ok hp h.lt h.fails (by rw [e]; exact k₃)
      (by rw [p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide), h.cnt]) r₃ (y₃.trans (y₂.trans (y₁.trans h.sy)))
  · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    have hnu : P.c.nums = 2 := by rw [hz.nums, hwd]; rfl
    have hfT : P.c.fT = P.c.fH + 8 * P.kit.nw := by rw [Cfg.fT, P.hnw]
    have hfr := hzQ.2.2.2.1.1
    rw [hnu] at hfr
    refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (candW_ok hp hwd h.kvh h.sy) fun t₁ ⟨k₁, T₁, p₁⟩ y₁ => ?_)
    refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreArgs_ok hp k₁ (y₁.trans h.sy) (ko := P.c.fT)
      ⟨by omega, by omega⟩) fun t₂ ⟨k₂, p₂, m₂, a₂⟩ y₂ => ?_)
    have hc : candI P s₀ i = Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2 ++
        (Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2) ++ []) :=
      congrArg Prod.fst (genT_two P hwd _ _)
    have hT : bytesAt t₂.mem (sA s₀ P.c.fT) P.Q = (candI P s₀ i).take P.Q := by
      rw [m₂, T₁, hc, List.append_nil]
    have hl : P.Q ≤ (candI P s₀ i).length := by
      have := congrArg List.length hT
      rw [bytesAt_length, List.length_take] at this
      omega
    refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreCall_ok hp k₂ (sg_eqW hp hwd k₂.kr hT hl) a₂)
      fun t₃ ⟨k₃, p₃, r₃⟩ y₃ => ?_)
    have e : (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (kvI P s₀ i).1 (nb P) (kvI P s₀ i).2).2 =
        Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2) :=
      congrArg Prod.snd (genT_two P hwd _ _)
    exact tryRest_ok hp h.lt h.fails (by rw [e]; exact k₃)
      (by rw [p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide), h.cnt]) r₃ (y₃.trans (y₂.trans (y₁.trans h.sy)))

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
      let K₁ := Spec.Hmac.hmac P.hH.SH.H (List.replicate P.c.D 0)
        (List.replicate P.c.D 1 ++ BitVec.ofNat 8 0 :: (dB P s₀ ++ hSpec P s₀))
      let V₁ := Spec.Hmac.hmac P.hH.SH.H K₁ (List.replicate P.c.D 1)
      let K₂ := Spec.Hmac.hmac P.hH.SH.H K₁ (V₁ ++ BitVec.ofNat 8 1 :: (dB P s₀ ++ hSpec P s₀))
      (K₂, Spec.Hmac.hmac P.hH.SH.H K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.kit.E.curve (xOf P s₀) = dB P s₀ := by
    have hnb : Spec.Ecdsa.nBits P.kit.E.curve + P.kit.sh = 8 * P.Q := P.kit.nbits
    have := P.kit.sh8
    rw [Spec.Ecdsa.Rfc6979.int2octets, VG.Proof.Ecdsa.Rfc6979.rlenR (R := P.Q) (by omega) (by omega),
      show P.Q = (dB P s₀).length from (bytesAt_length _ _ _).symm, VG.Proof.Ecdsa.Rfc6979.toBytes_ofBytes]
  simp only [kv0, Spec.Ecdsa.Rfc6979.init, hi]
  rfl

theorem stores_ok {s₀ : State} (hp : Pre P s₀) {W : Nat} (hW : fK + 8 * W ≤ P.c.frB) :
    ∀ (l : List Nat) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ j ∈ l, j < W) → KR P s₀ s →
    (∀ t, KR P s₀ t → t.gpr = s.gpr → Frame [sR s₀ fK (8 * W)] s.mem t.mem → WP isa (.block rest) t Q) →
    WP isa (.block (l.map (fun j => .store .d .t0 .s1 (fK + 8 * j)) ++ rest)) s Q
  | [], s, rest, Q, _, h, k => k s h rfl (Frame.refl _ _)
  | j :: l, s, rest, Q, hl, h, k => by
    have hj := hl j (by simp)
    have hzQ := (sizes P).Q
    have := (sizes P).H
    have hcn : P.c.nw = P.kit.nw := P.hnw
    have hfK : fK = 64 := rfl
    simp only [List.map_cons, List.cons_append]
    refine VG.RISCV64.Steps.wp_sd (a := sA s₀ (fK + 8 * j)) (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega) (by rw [h.s1])
      (by
        show (s₀.sp + BitVec.ofNat 64 (fK + 8 * j)).toNat % 8 = 0
        rw [VG.Offset.toNat_add_ofNat]
        have := hp.al; have := hp.top
        simp only [fK] at *
        omega)
      (in_fr hp h.wr (by simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega)) fun t₁ m₁ => ?_
    have F₁ : Frame [sR s₀ fK (8 * W)] s.mem t₁.mem := by
      rw [m₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains s₀.sp (d := fK + 8 * j) (n := 8) (e := fK) (k := 8 * W) (by omega)
          (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega) (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega))
    have k₁ : KR P s₀ t₁ := h.keep m₁.rd m₁.wr m₁.sp (fun r _ => by rw [m₁.gpr]) F₁
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj (.inl (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega)) (by decide) (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, part_sub (P := P) (by simp only [fK]; have := (sizes P).H; have := (sizes P).Q; omega)⟩)
    exact stores_ok hp hW l (fun j' hj' => hl j' (by simp [hj'])) k₁ fun t h' g f =>
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
      ResultIs P s₀ (sigI P s₀ i) u := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.main
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (prologue_ok hp) fun s₁ h₁ y₁ => ?_)
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (reduceAny_ok hp h₁) fun s₂ ⟨h₂, hh₂⟩ y₂ => ?_)
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (initKV_ok hp h₂ hh₂) fun s₃ h₃ y₃ => ?_)
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (rekeyFull_ok hp h₃ (y₃.trans (y₂.trans y₁)) (b := 0) (by decide))
    fun s₄ h₄ y₄ => ?_)
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (rekeyFull_ok hp h₄ (y₄.trans (y₃.trans (y₂.trans y₁))) (b := 1) (by decide))
    fun s₅ h₅ y₅ => ?_)
  refine WP.seq ?_
  unfold Cfg.initCnt
  refine VG.Proof.Ecdsa.RISCV64.Comb.WP.of_syms (wp_li (imm := P.c.tries) P.hT' fun s₆ u₆ =>
    WP.block_nil fun y₆ => ?_)
  have L₆ : LoopInv P s₀ 0 s₆ := by
    have e := kv0_eq P s₀
    refine ⟨P.hT, ⟨h₅.kr.upd (by decide) u₆, ?_, ?_, ?_⟩, by rw [u₆.gpr, Nat.sub_zero], fun j hj => absurd hj (by omega),
      y₆.trans (y₅.trans (y₄.trans (y₃.trans (y₂.trans y₁))))⟩
    · rw [u₆.mem, h₅.k]; show _ = (kv0 P s₀).1; rw [e]
    · rw [u₆.mem, h₅.v]; show _ = (kv0 P s₀).2; rw [e]
    · rw [u₆.mem]; exact h₅.h
  refine WP.seq (WP.mono (loop_ok hp L₆) fun s₇ ⟨i, x₇⟩ => ?_)
  rw [Cfg.wipe, List.cons_append]
  have hzQ := hz.Q
  have := hz.H
  have hW : fK + 8 * ((P.c.fH - fK) / 8 + P.c.nw * P.c.nums) ≤ P.c.frB := by
    have h1 := hz.Q.2.2.2.1.1
    rw [P.hnw]
    rcases (show P.c.nums = 1 ∨ P.c.nums = 2 by rw [hz.nums]; split <;> simp) with h | h <;>
      rw [h] at h1 ⊢ <;> simp only [fK] <;> omega
  refine wp_li (imm := 0) (by decide) fun s₈ u₈ => ?_
  refine stores_ok hp hW (List.range ((P.c.fH - fK) / 8 + P.c.nw * P.c.nums)) (fun j hj => List.mem_range.mp hj)
    (x₇.kr.upd (by decide) u₈)
    fun s₉ k₉ g₉ f₉ => ?_
  refine WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp.al]) k₉.s1
    (by decide) restorable
    (fun q hq => in_fr' hp k₉.wr (by
      simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega))
    (k₉.saved.sub (by decide))) fun u hr => ⟨fun r hr' => ?_, ?_, by rw [hr.sp, k₉.sp], by rw [hr.wr, k₉.wr],
      i, x₇.lt, x₇.fails, x₇.last, ?_⟩
  · refine hr.gpr_of ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [.inl (by decide), .inl (by decide), .inl (by decide), .inl (by decide), .inl (by decide),
      .inl (by decide), .inl (by decide), .inr (k₉.nv _ (by simp)), .inr (k₉.nv _ (by simp)),
      .inr (k₉.nv _ (by simp)), .inr (k₉.nv _ (by simp)), .inr (k₉.nv _ (by simp))]
  · exact hr.gpr_of (.inl (by decide))
  · refine x₇.res.keep ?_ ?_
    · rw [hr.other _ (by decide), g₉, u₈.other _ (by decide)]
    · rw [hr.mem, fbytes f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.f_o.sub_left (part_sub hW)).symm) (by omega), u₈.mem]

end

/-! ## The frame -/

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hp : (rfcRC P.kit.K P.I P.H P.c.f P.N).pre s) : Pre P (allocd P.c.frB s) := by
  have hz := sizes P
  have hzH := hz.H
  have hX := hz.X
  have hlen : P.I.ecdsa.curve.len = P.Q := by rw [P.hE, P.kit.len]
  obtain ⟨hs, hk⟩ := hp
  simp only [rfcR, hlen, P.hD, stripConsts_gpr, stripConsts_sp, stripConsts_wr] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25⟩ := hs
  have hN : P.N = P.c.frB + P.X := rfl
  have hspN : (s.sp - BitVec.ofNat 64 P.c.frB).toNat = s.sp.toNat - P.c.frB :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by rw [hN] at h9; omega) (by have := hz.Q; omega)
  have subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 P.c.frB, P.c.frB⟩ (below s.sp P.N) :=
    Offset.sub_below s.sp (by rw [hN]; omega) (by rw [hN]; omega)
  have subS : Region.Sub (below (s.sp - BitVec.ofNat 64 P.c.frB) P.X) (below s.sp P.N) := by
    have := below_body' s.sp P.c.frB P.X
    rwa [Nat.add_comm P.X, ← hN] at this
  refine ⟨?_, ?_, h3, h4, h5, h6, h7, h10.sub_left subF, h11.sub_left subF, h12.sub_left subF, h13.sub_left subF,
    h10.sub_left subS, h11.sub_left subS, h12.sub_left subS, h13.sub_left subS, ?_, ?_, ?_, h14, h15, h16, h17, h18,
    hk.2.1, hk.2.2.2, fun t ht => (hk.2.2.1 t ht).1, ?_, ?_, h22, h23, h24, h25⟩
  · have e1 : s.rd.take (s.rd.length - P.kit.K.length) = [⟨s.gpr .a1, P.Q⟩, ⟨s.gpr .a2, P.c.D⟩, ⟨s.gpr .a5, 40⟩] := h1
    have e := List.take_append_drop (s.rd.length - P.kit.K.length) s.rd
    rw [e1, hk.1] at e
    show s.rd = _
    rw [← e]; rfl
  · show (⟨s.sp - BitVec.ofNat 64 P.c.frB, P.c.frB⟩ : Region) :: s.wr = _
    rw [h2]; rfl
  · show (s.sp - BitVec.ofNat 64 P.c.frB).toNat % 16 = 0
    rw [hspN]; have := (sizes P).Q; have := (sizes P).H; omega
  · show P.X ≤ (s.sp - BitVec.ofNat 64 P.c.frB).toNat
    rw [hspN]; rw [hN] at h9; omega
  · show (s.sp - BitVec.ofNat 64 P.c.frB).toNat + P.c.frB ≤ 2 ^ 64
    rw [hspN]; have := s.sp.isLt; rw [hN] at h9; omega
  · intro t ht r hr
    obtain ⟨-, hw, hres⟩ := hk.2.2.1 t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hb : below s.sp P.N ∈ abi.reserved P.N s := by
      show _ ∈ stackBelow s.sp P.N
      rw [show P.N = (P.c.frB - 1 + P.X) + 1 by rw [hN]; have := (sizes P).Q; have := (sizes P).H; omega]
      exact List.mem_singleton_self _
    have d1 : Region.Disjoint t (below s.sp P.N) := hres _ hb
    rcases hr with rfl | rfl | rfl | rfl
    · exact (d1.symm.sub_left subF).symm
    · exact hw _ (by rw [h2]; exact List.mem_cons_self)
    · exact hw _ (by rw [h2]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    · exact (d1.symm.sub_left subS).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (h21.sub_left subF).symm
    · exact h19
    · exact h20
    · exact (h21.sub_left subS).symm

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold (s₀ : State) :
    result P.I s₀.mem (dk s₀) (dg s₀) =
      if 1 ≤ xOf P s₀ ∧ xOf P s₀ < P.kit.E.curve.n then
        Spec.Ecdsa.Rfc6979.search P.kit.E.curve P.hH.SH.H P.c.D (xOf P s₀) (eOf P s₀) (kv0 P s₀).1 (kv0 P s₀).2
          P.c.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.sign, P.hct]
  rw [P.hE, P.hHash, P.hD, P.kit.len]
  rfl

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq (s₀ : State) {i : Nat} (hi : i < P.c.tries) (hf : ∀ j < i, sigI P s₀ j = none)
    (hl : sigI P s₀ i ≠ none ∨ i + 1 = P.c.tries) :
    (result P.I s₀.mem (dk s₀) (dg s₀)).1 = sigI P s₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P s₀ ∧ xOf P s₀ < P.kit.E.curve.n
  · simp only [hv, and_self, ite_true]
    rw [VG.Proof.Ecdsa.Rfc6979.searchB_shift (b := nb P) rfl i P.c.tries (by omega) hf,
      show P.c.tries - i = (P.c.tries - 1 - i) + 1 by omega]
    cases hs : sigI P s₀ i with
    | some rs => rw [VG.Proof.Ecdsa.Rfc6979.searchB_ok (b := nb P) rfl hs]
    | none =>
      have h7 : i + 1 = P.c.tries := hl.resolve_left (by simp [hs])
      rw [VG.Proof.Ecdsa.Rfc6979.searchB_fail (b := nb P) rfl hs, show P.c.tries - 1 - i = 0 by omega]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-- The function, in its frame. -/
theorem correct {s : State} (hp : (rfcRC P.kit.K P.I P.H P.c.f P.N).pre s) :
    WP isa P.c.sign s fun s' => abiPreserved s s' ∧ (rfcRC P.kit.K P.I P.H P.c.f P.N).post s s' := by
  have hz := sizes P
  have hzH := hz.H
  have hsp : P.N ≤ s.sp.toNat := hp.1.2.2.2.2.2.2.2.2.1
  have p := pre_alloc hp
  unfold Cfg.sign
  have hQ := hz.Q
  refine WP.alloc ⟨by omega, by omega, by omega⟩
    (by have : P.c.frB ≤ P.N := Nat.le_add_right _ _; omega)
    (WP.mono (main_ok p) fun s' ⟨hk, hra, hsp', hwr, i, hi, hf, hl, hres⟩ => ?_)
  rw [freed_eq hwr hsp']
  refine ⟨⟨fun r hr => hk r hr, rfl, hra⟩, ?_⟩
  have hlen : P.I.ecdsa.curve.len = P.Q := by rw [P.hE, P.kit.len]
  have hr := result_eq (s₀ := allocd P.c.frB s) hi hf hl
  show match (result P.I s.mem (s.gpr .a1) (s.gpr .a2)).1 with
    | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * P.I.ecdsa.curve.len) = Spec.Ecdsa.encode P.I.ecdsa.curve rs
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * P.I.ecdsa.curve.len) = List.replicate (2 * P.I.ecdsa.curve.len) 0
  rw [show s.mem = (allocd P.c.frB s).mem from rfl, show s.gpr = (allocd P.c.frB s).gpr from rfl, hr, hlen, P.hE]
  unfold ResultIs at hres
  split at hres <;> exact ⟨by rw [hres.1]; rfl, hres.2⟩

end VG.Proof.Ecdsa.Rfc6979.RISCV64
