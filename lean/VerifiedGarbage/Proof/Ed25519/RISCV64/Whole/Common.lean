module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# Ed25519's whole functions on RISC-V: what they share

The calls of SHA-512's streaming functions on the state at `scratch` (`sc`),
with their arguments set (`hashInit_ok`, `hashUpdate_ok`,
`hashFinalize_ok`), from HMAC's lemmas about them (`HashOK`): `update` and
`finalize` keep their working space in frames in the 208 bytes below the
stack pointer. Also the instructions that set a count or a length (`Sets`)
and those that set the arguments of a call (`args3_ok`, `args5_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)

/-- SHA-512's streaming functions, as HMAC's proofs know them (`Proof.Hmac.Stream.RISCV64.Sha512.hash`). -/
def shaHash : Impl.Hmac.Stream.RISCV64.Hash where
  b := 7
  N := 64
  D := 64
  F := 208
  initN := Spec.Sha512.init512Api.name
  initC := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512
  updN := Spec.Sha512.updateApi.name
  updC := Impl.Sha512.RISCV64.Stream.update
  finN := Spec.Sha512.finalizeApi.name
  finC := Impl.Sha512.RISCV64.Stream.finalize

/-- What the proofs need of SHA-512's streaming functions: HMAC's facts about them
(`Proof.Hmac.Stream.RISCV64.Sha512.ok`), whose states are SHA-512's and whose digest is SHA-512's.
The proofs take it as an argument, so that only the modules stating the functions' contracts
import SHA-512's proofs. -/
structure ShaOK where
  ok : HashOK shaHash
  repr : ok.SH.Repr = Spec.Sha512.Repr Spec.Sha512.H0_512
  fh : ok.SH.H.hash = Spec.Sha512.sha512

/-- The streaming state at `p` represents the message `m`. -/
abbrev Repr (m : Mem) (p : Addr) (x : List Byte) : Prop := Spec.Sha512.Repr Spec.Sha512.H0_512 m p x

/-! ## Setting a register -/

/-- `is` sets `d` to `v` of the registers, and nothing else. -/
def Sets (is : List Instr) (d : Reg) (v : (Reg → BitVec 64) → BitVec 64) : Prop :=
  ∀ (rest : List Instr) (u : State) (Q : State → Prop),
    (∀ u', Upd u u' d (v u.gpr) → WP isa (.block rest) u' Q) → WP isa (.block (is ++ rest)) u Q

theorem Sets.li {d : Reg} {k : Nat} (h : k < 2048) : Sets [.li d k] d fun _ => BitVec.ofNat 64 k :=
  fun _ _ _ hk => wp_li h hk

theorem Sets.addi {d n : Reg} {k : Nat} (h : k < 2048) :
    Sets [.addi d n k] d fun g => g n + BitVec.ofNat 64 k :=
  fun _ _ _ hk => wp_addi h hk

theorem Sets.mov {d n : Reg} : Sets [mov d n] d fun g => g n :=
  fun _ _ _ hk => wp_mv hk

/-! ## The calls -/

/-- The scratch space at `sc` and the 208 bytes below the stack pointer that the callees' frames take. -/
structure ScEnv (sc : Addr) (t : State) : Prop where
  w : (⟨sc, 8192⟩ : Region) ∈ t.wr
  al : t.sp.toNat % 16 = 0
  sp : 208 ≤ t.sp.toNat
  d : (below t.sp 208).Disjoint ⟨sc, 8192⟩

theorem ScEnv.of {sc : Addr} {t u : State} (h : ScEnv sc t) (hw : u.wr = t.wr) (hs : u.sp = t.sp) :
    ScEnv sc u :=
  ⟨hw ▸ h.w, hs ▸ h.al, hs ▸ h.sp, hs ▸ h.d⟩

theorem sub_sc0 (sc : Addr) {n : Nat} (h : n ≤ 8192) : Region.Sub ⟨sc, n⟩ ⟨sc, 8192⟩ := by
  simpa using Offset.sub_base sc (d := 0) (n := n) (k := 8192) (by omega)

theorem cov_sc0 {ws : List Region} {sc : Addr} (hw : (⟨sc, 8192⟩ : Region) ∈ ws) {n : Nat} (h : n ≤ 8192) :
    Covers [⟨sc, n⟩] ws :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, hw, 0, by simp, by simpa using h⟩

theorem frame_hash {sc sp : Addr} {m m' : Mem} (h : Frame ([⟨sc, 192⟩] ++ [below sp 208]) m m') :
    Frame [⟨sc, 8192⟩, below sp 208] m m' :=
  h.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sc0 sc (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

theorem Covers.app {xs ys ws : List Region} (h₁ : Covers xs ws) (h₂ : Covers ys ws) : Covers (xs ++ ys) ws := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁ a n ⟨r, hr, hc⟩
  · exact h₂ a n ⟨r, hr, hc⟩

theorem pres_args {r : Reg} (hr : r ∈ preserved) : r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 := by
  revert hr; cases r <;> decide

/-- `init` of the state at `sc`, in `sr`. -/
theorem hashInit_ok (C : ShaOK) {t : State} {sr : Reg} {sc : Addr} (hs : t.gpr sr = sc) (he : ScEnv sc t)
    {Q : State → Prop}
    (k : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → Frame [⟨sc, 8192⟩, below t.sp 208] t.mem t'.mem →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) → Repr t'.mem sc [] → Q t') :
    WP isa (hashInit sr) t Q := by
  refine WP.seq (wp_mv fun u hu => WP.block_nil ?_)
  have h0 : u.gpr .a0 = sc := by rw [hu.gpr, hs]
  refine C.ok.callInit_ok h0
    (by rw [hu.wr, hu.rd]; exact cov_sc0 (List.mem_append_right _ he.w) (by decide))
    (by rw [hu.wr]; exact cov_sc0 he.w (by decide)) fun t' h₁ h₂ h₃ hf hp hr => ?_
  refine k t' (h₁.trans hu.rd) (h₂.trans hu.wr) (h₃.trans hu.sp) ?_ (fun r hr => ?_) (by rw [C.repr] at hr; exact hr)
  · rw [← hu.mem, ← hu.sp]
    exact frame_hash hf
  · rw [hp r hr, hu.other r fun e => (pres_args hr).1 e]

/-- `update` of the state at `sc` (in `sr`) with the `len` bytes at `dat` (`off(src)`), the count
set by `cnt` and the length by `ln`. -/
theorem hashUpdate_ok (C : ShaOK) {t : State} {sr src : Reg} {sc dat : Addr} {cnt ln : List Instr}
    {vc vl : (Reg → BitVec 64) → BitVec 64} {off len : Nat}
    (hsr' : sr ≠ .a0 ∧ sr ≠ .a1 ∧ sr ≠ .a2 ∧ sr ≠ .a3)
    (hsrc' : src ≠ .a0 ∧ src ≠ .a1) (hoff : off < 2048)
    (hs : t.gpr sr = sc) (hd : t.gpr src + BitVec.ofNat 64 off = dat)
    (hcnt : Sets cnt .a1 vc) (hln : Sets ln .a3 vl)
    (hvc : ∀ g g' : Reg → BitVec 64, (∀ r, r ≠ .a0 → g r = g' r) → vc g = vc g')
    (hvl : ∀ g g' : Reg → BitVec 64, (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → g r = g' r) → vl g = vl g')
    (hl : (vl t.gpr).toNat = len) (he : ScEnv sc t)
    (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr)) (hdsc : Region.Disjoint ⟨dat, len⟩ ⟨sc, 8192⟩)
    (hdsp : (below t.sp 208).Disjoint ⟨dat, len⟩) {Q : State → Prop}
    (k : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → Frame [⟨sc, 8192⟩, below t.sp 208] t.mem t'.mem →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      (∀ m, Repr t.mem sc m → vc t.gpr = BitVec.ofNat 64 m.length →
        Repr t'.mem sc (m ++ Spec.Ed25519.bytesAt t.mem dat len)) → Q t') :
    WP isa (hashUpdate sr cnt src off ln) t Q := by
  unfold hashUpdate
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun u₁ h₁ => hcnt _ u₁ _ fun u₂ h₂ =>
    wp_addi hoff fun u₃ h₃ => ?_)
  rw [← List.append_nil ln]
  refine hln [] u₃ _ fun u₄ h₄ => WP.block_nil ?_
  obtain ⟨s0, s1, s2, s3⟩ := hsr'
  have g0 : u₄.gpr .a0 = sc := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, hs]
  have g1 : u₄.gpr .a1 = vc t.gpr := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
    exact hvc _ _ fun r hr => h₁.other r hr
  have g2 : u₄.gpr .a2 = dat := by
    rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ hsrc'.2, h₁.other _ hsrc'.1, hd]
  have g3 : (u₄.gpr .a3).toNat = len := by
    rw [h₄.gpr, ← hl]
    congr 1
    exact hvl _ _ fun r r0 r1 r2 => by rw [h₃.other r r2, h₂.other r r1, h₁.other r r0]
  have grd : u₄.rd = t.rd := by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  have gwr : u₄.wr = t.wr := by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  have gsp : u₄.sp = t.sp := by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  have gm : u₄.mem = t.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have gp : ∀ r ∈ preserved, u₄.gpr r = t.gpr r := fun r hr => by
    obtain ⟨p0, p1, p2, p3, -⟩ := pres_args hr
    rw [h₄.other _ p3, h₃.other _ p2, h₂.other _ p1, h₁.other _ p0]
  have hb : (below u₄.sp 208).Disjoint ⟨sc, 8192⟩ := gsp ▸ he.d
  refine C.ok.callUpd_ok g0 g2 g3 (hdsc.sub_right (sub_sc0 sc (by decide))) (gsp ▸ he.al) (gsp ▸ he.sp)
    (hb.sub_right (sub_sc0 sc (by decide))) (gsp ▸ hdsp)
    (by rw [grd, gwr]; exact Covers.app hdc (cov_sc0 (List.mem_append_right _ he.w) (by decide)))
    (by rw [gwr]; exact cov_sc0 he.w (by decide)) fun t' e₁ e₂ e₃ hf hp hr => ?_
  refine k t' (e₁.trans grd) (e₂.trans gwr) (e₃.trans gsp) (by rw [← gm, ← gsp]; exact frame_hash hf)
    (fun r hr => (hp r hr).trans (gp r hr)) fun m hm hc => ?_
  rw [C.repr] at hr
  have := hr m (by rw [gm]; exact hm) (by rw [g1]; exact hc)
  rw [gm] at this
  exact this

/-- `finalize` of the state at `sc` (in `sr`) into the 64 bytes at `o(f)`, the count set by `cnt`. -/
theorem hashFinalize_ok (C : ShaOK) {t : State} {sr f : Reg} {sc out : Addr} {cnt : List Instr}
    {vc : (Reg → BitVec 64) → BitVec 64} {o : Nat}
    (hsr' : sr ≠ .a0 ∧ sr ≠ .a1 ∧ sr ≠ .a2) (hf' : f ≠ .a0 ∧ f ≠ .a1)
    (ho : o < 2048) (hs : t.gpr sr = sc) (hd : t.gpr f + BitVec.ofNat 64 o = out)
    (hcnt : Sets cnt .a1 vc) (hvc : ∀ g g' : Reg → BitVec 64, (∀ r, r ≠ .a0 → g r = g' r) → vc g = vc g')
    (he : ScEnv sc t) (hdw : Covers [⟨out, 64⟩] t.wr) (hdsc : Region.Disjoint ⟨out, 64⟩ ⟨sc, 8192⟩)
    (hdsp : (below t.sp 208).Disjoint ⟨out, 64⟩) {Q : State → Prop}
    (k : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → Frame [⟨sc, 8192⟩, ⟨out, 64⟩, below t.sp 208] t.mem t'.mem →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      (∀ m, Repr t.mem sc m → m.length < 2 ^ 64 → vc t.gpr = BitVec.ofNat 64 m.length →
        Spec.Ed25519.bytesAt t'.mem out 64 = Spec.Sha512.sha512 m) → Q t') :
    WP isa (hashFinalize sr cnt f o) t Q := by
  unfold hashFinalize
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun u₁ h₁ => hcnt _ u₁ _ fun u₂ h₂ =>
    wp_addi ho fun u₃ h₃ => WP.block_nil ?_)
  obtain ⟨s0, s1, s2⟩ := hsr'
  have g0 : u₃.gpr .a0 = sc := by
    rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, hs]
  have g1 : u₃.gpr .a1 = vc t.gpr := by
    rw [h₃.other _ (by decide), h₂.gpr]
    exact hvc _ _ fun r hr => h₁.other r hr
  have g2 : u₃.gpr .a2 = out := by
    rw [h₃.gpr, h₂.other _ hf'.2, h₁.other _ hf'.1, hd]
  have grd : u₃.rd = t.rd := by rw [h₃.rd, h₂.rd, h₁.rd]
  have gwr : u₃.wr = t.wr := by rw [h₃.wr, h₂.wr, h₁.wr]
  have gsp : u₃.sp = t.sp := by rw [h₃.sp, h₂.sp, h₁.sp]
  have gm : u₃.mem = t.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have gp : ∀ r ∈ preserved, u₃.gpr r = t.gpr r := fun r hr => by
    obtain ⟨p0, p1, p2, -, -⟩ := pres_args hr
    rw [h₃.other _ p2, h₂.other _ p1, h₁.other _ p0]
  have hb : (below u₃.sp 208).Disjoint ⟨sc, 8192⟩ := gsp ▸ he.d
  have hcw : Covers [⟨sc, 192⟩, ⟨out, 64⟩] u₃.wr := by
    rw [gwr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_sc0 he.w (by decide) a n ⟨_, List.mem_cons_self, hc⟩
    · exact hdw a n ⟨_, List.mem_cons_self, hc⟩
  refine C.ok.callFin_ok g0 g2 (hdsc.sub_right (sub_sc0 sc (by decide))).symm (gsp ▸ he.al) (gsp ▸ he.sp)
    (hb.sub_right (sub_sc0 sc (by decide))) (gsp ▸ hdsp)
    (fun a n h => by obtain ⟨r, hr, hc⟩ := hcw a n h; exact ⟨r, List.mem_append_right _ hr, hc⟩) hcw
    fun t' e₁ e₂ e₃ hf hp hr => ?_
  refine k t' (e₁.trans grd) (e₂.trans gwr) (e₃.trans gsp) ?_
    (fun r hr => (hp r hr).trans (gp r hr)) fun m hm hl hc => ?_
  · rw [← gm, ← gsp]
    exact hf.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, sub_sc0 sc (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · rw [C.repr, C.fh] at hr
    exact hr m (by rw [gm]; exact hm) hl (by rw [g1]; exact hc)

/-- Disjoint regions fit in the address space together. -/
theorem len_add_le {a b : Addr} {n k : Nat} (hn' : n ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) (h : Region.Disjoint ⟨a, n⟩ ⟨b, k⟩) :
    n + k ≤ 2 ^ 64 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hn : 0 < n := by omega
  have hk0 : 0 < k := by omega
  by_cases hd : (b - a).toNat < n
  · refine h b ?_ ?_
    · show (b - a).toNat + 1 ≤ n; omega
    · show (b - b).toNat + 1 ≤ k; rw [BitVec.sub_self, BitVec.toNat_zero]; omega
  · have hlt' := (b - a).isLt
    refine h (b + BitVec.ofNat 64 (2 ^ 64 - (b - a).toNat)) ?_ ?_
    · show (b + BitVec.ofNat 64 (2 ^ 64 - (b - a).toNat) - a).toNat + 1 ≤ n
      have e : b + BitVec.ofNat 64 (2 ^ 64 - (b - a).toNat) - a =
          (b - a) + BitVec.ofNat 64 (2 ^ 64 - (b - a).toNat) := by
        rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 _),
          ← BitVec.add_assoc]
      rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
      have : ((b - a).toNat + (2 ^ 64 - (b - a).toNat) % 2 ^ 64) % 2 ^ 64 = 0 := by
        by_cases h0 : (b - a).toNat = 0
        · simp [h0]
        · rw [Nat.mod_eq_of_lt (by omega : 2 ^ 64 - (b - a).toNat < 2 ^ 64)]
          rw [show (b - a).toNat + (2 ^ 64 - (b - a).toNat) = 2 ^ 64 by omega]
      omega
    · show (b + BitVec.ofNat 64 (2 ^ 64 - (b - a).toNat) - b).toNat + 1 ≤ k
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      have : (2 ^ 64 - (b - a).toNat) % 2 ^ 64 ≤ 2 ^ 64 - (b - a).toNat := Nat.mod_le _ _
      omega

/-- What a block setting argument registers keeps. -/
structure ArgsKeep (t u : State) : Prop where
  mem : u.mem = t.mem
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  pres : ∀ r ∈ preserved, u.gpr r = t.gpr r

/-- Three arguments, `a0`–`a2`, each an `addi` of a callee-saved register. -/
theorem args3_ok {t : State} {a b c : Reg} {i j k : Nat}
    (hi : i < 2048) (hj : j < 2048) (hk : k < 2048) (hb : b ∈ preserved) (hc : c ∈ preserved)
    {Q : State → Prop}
    (K : ∀ u, ArgsKeep t u → u.gpr .a0 = t.gpr a + BitVec.ofNat 64 i → u.gpr .a1 = t.gpr b + BitVec.ofNat 64 j →
      u.gpr .a2 = t.gpr c + BitVec.ofNat 64 k → Q u) :
    WP isa (.block [.addi .a0 a i, .addi .a1 b j, .addi .a2 c k]) t Q := by
  have pb := pres_args hb
  have pc := pres_args hc
  exact wp_addi hi fun u₁ h₁ => wp_addi hj fun u₂ h₂ => wp_addi hk fun u₃ h₃ => WP.block_nil <|
    K u₃ ⟨by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.rd, h₂.rd, h₁.rd], by rw [h₃.wr, h₂.wr, h₁.wr],
      by rw [h₃.sp, h₂.sp, h₁.sp], fun r hr => by
        obtain ⟨p0, p1, p2, -, -⟩ := pres_args hr
        rw [h₃.other _ p2, h₂.other _ p1, h₁.other _ p0]⟩
      (by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr])
      (by rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ pb.1])
      (by rw [h₃.gpr, h₂.other _ pc.2.1, h₁.other _ pc.1])

/-- Five arguments, `a0`–`a4`, each an `addi` of a callee-saved register. -/
theorem args5_ok {t : State} {a b c d e : Reg} {i j k l n : Nat}
    (hi : i < 2048) (hj : j < 2048) (hk : k < 2048) (hl : l < 2048)
    (hn : n < 2048) (hs : ∀ x ∈ [b, c, d, e], x ∈ preserved) {Q : State → Prop}
    (K : ∀ u, ArgsKeep t u → u.gpr .a0 = t.gpr a + BitVec.ofNat 64 i → u.gpr .a1 = t.gpr b + BitVec.ofNat 64 j →
      u.gpr .a2 = t.gpr c + BitVec.ofNat 64 k → u.gpr .a3 = t.gpr d + BitVec.ofNat 64 l →
      u.gpr .a4 = t.gpr e + BitVec.ofNat 64 n → Q u) :
    WP isa (.block [.addi .a0 a i, .addi .a1 b j, .addi .a2 c k, .addi .a3 d l, .addi .a4 e n]) t Q := by
  have pb := pres_args (hs b (by simp))
  have pc := pres_args (hs c (by simp))
  have pd := pres_args (hs d (by simp))
  have pe := pres_args (hs e (by simp))
  exact wp_addi hi fun u₁ h₁ => wp_addi hj fun u₂ h₂ => wp_addi hk fun u₃ h₃ =>
    wp_addi hl fun u₄ h₄ => wp_addi hn fun u₅ h₅ => WP.block_nil <|
    K u₅ ⟨by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
      by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp], fun r hr => by
        obtain ⟨p0, p1, p2, p3, p4⟩ := pres_args hr
        rw [h₅.other _ p4, h₄.other _ p3, h₃.other _ p2, h₂.other _ p1, h₁.other _ p0]⟩
      (by rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr])
      (by rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ pb.1])
      (by rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.other _ pc.2.1, h₁.other _ pc.1])
      (by rw [h₅.other _ (by decide), h₄.gpr, h₃.other _ pd.2.2.1, h₂.other _ pd.2.1, h₁.other _ pd.1])
      (by rw [h₅.gpr, h₄.other _ pe.2.2.2.1, h₃.other _ pe.2.2.1, h₂.other _ pe.2.1, h₁.other _ pe.1])

/-- A count after a message of length `x`. -/
theorem cnt_eq (x : BitVec 64) (c : Nat) : x + BitVec.ofNat 64 c = BitVec.ofNat 64 (c + x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.Ed25519.RISCV64.Whole
