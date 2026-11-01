module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Ed25519's whole functions on PPC64LE: what they share

The calls of SHA-512's streaming functions on the state at `scratch` (`sc`),
whose working space follows it at `sc + 192`, with their arguments set
(`hashInit_ok`, `hashUpdate_ok`, `hashFinalize_ok`), from HMAC's lemmas
about them (`HashOK`); the instructions that set a count or a length
(`Sets`); and the register saves at `o(F)` (`slots`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

/-- SHA-512's streaming functions, as HMAC's proofs know them (`Proof.Hmac.Stream.PPC64LE.Sha512.hash`). -/
def shaHash : Impl.Hmac.Stream.PPC64LE.Hash where
  B := 128
  N := 64
  D := 64
  FD := 64
  W := 224
  initN := Spec.Sha512.init512Api.name
  initC := Impl.Sha512.PPC64LE.Stream.init Spec.Sha512.H0_512
  updN := Spec.Sha512.updateScratchApi.name
  updC := Impl.Sha512.PPC64LE.Stream.update
  finN := Spec.Sha512.finalizeScratchApi.name
  finC := Impl.Sha512.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_sha512_init_scratch"

/-- What the proofs need of SHA-512's streaming functions: HMAC's facts about them
(`Proof.Hmac.Stream.PPC64LE.Sha512.ok`), whose states are SHA-512's and whose digest is SHA-512's.
The proofs take it as an argument, so that only the modules stating the functions' contracts
import SHA-512's proofs. -/
structure ShaOK where
  ok : HashOK shaHash
  repr : ok.SH.Repr = Spec.Sha512.Repr Spec.Sha512.H0_512
  fh : ok.fh = Spec.Sha512.sha512

/-- The streaming state at `p` represents the message `m`. -/
abbrev Repr (m : Mem) (p : Addr) (x : List Byte) : Prop := Spec.Sha512.Repr Spec.Sha512.H0_512 m p x

/-! ## Setting a register -/

/-- `is` sets `d` to `v` of the registers, and nothing else. -/
def Sets (is : List Instr) (d : Reg) (v : (Reg → BitVec 64) → BitVec 64) : Prop :=
  ∀ (rest : List Instr) (u : State) (Q : State → Prop),
    (∀ u', Upd u u' d (v u.gpr) → u'.lr = u.lr → WP isa (.block rest) u' Q) → WP isa (.block (is ++ rest)) u Q

theorem Sets.li {d : Reg} {k : Nat} (h : k < 2 ^ 15) : Sets [.li d k] d fun _ => BitVec.ofNat 64 k :=
  fun _ _ _ hk => WP.cons (exec_li h) (hk _ (Upd.write _ _ _) rfl)

theorem Sets.addi {d n : Reg} {k : Nat} (hn : n ≠ .r0) (h : k < 2 ^ 15) :
    Sets [.addi d n k] d fun g => g n + BitVec.ofNat 64 k :=
  fun _ _ _ hk => WP.cons (exec_addi hn h) (hk _ (Upd.write _ _ _) rfl)

/-! ## The calls -/

/-- The scratch space at `sc` and the 48 bytes below the stack pointer that the callees' frames take. -/
structure ScEnv (sc : Addr) (t : State) : Prop where
  w : (⟨sc, 8192⟩ : Region) ∈ t.wr
  sp : 48 ≤ t.sp.toNat
  d : (below t.sp 48).Disjoint ⟨sc, 8192⟩

theorem ScEnv.of {sc : Addr} {t u : State} (h : ScEnv sc t) (hw : u.wr = t.wr) (hs : u.sp = t.sp) :
    ScEnv sc u :=
  ⟨hw ▸ h.w, hs ▸ h.sp, hs ▸ h.d⟩

theorem sub_sc (sc : Addr) {d n : Nat} (h : d + n ≤ 8192) : Region.Sub ⟨sc + BitVec.ofNat 64 d, n⟩ ⟨sc, 8192⟩ :=
  Offset.sub_base sc h

theorem sub_sc0 (sc : Addr) {n : Nat} (h : n ≤ 8192) : Region.Sub ⟨sc, n⟩ ⟨sc, 8192⟩ := by
  simpa using Offset.sub_base sc (d := 0) (n := n) (k := 8192) (by omega)

theorem cov_sc {ws : List Region} {sc : Addr} (hw : (⟨sc, 8192⟩ : Region) ∈ ws) {d n : Nat} (h : d + n ≤ 8192) :
    ∃ r' ∈ ws, ∃ off, (⟨sc + BitVec.ofNat 64 d, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨sc + BitVec.ofNat 64 d, n⟩ : Region).len ≤ r'.len :=
  ⟨_, hw, d, rfl, h⟩

theorem cov_sc0 {ws : List Region} {sc : Addr} (hw : (⟨sc, 8192⟩ : Region) ∈ ws) {n : Nat} (h : n ≤ 8192) :
    ∃ r' ∈ ws, ∃ off, (⟨sc, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨sc, n⟩ : Region).len ≤ r'.len :=
  ⟨_, hw, 0, by simp, by simpa using h⟩

theorem r3_pres : Reg.r3 ∉ preserved := by decide

/-- `init` of the state at `sc`, in `sr`. -/
theorem hashInit_ok (C : ShaOK) {t : State} {sr : Reg} {sc : Addr} (hsr : sr ≠ .r0) (hs : t.gpr sr = sc) (he : ScEnv sc t)
    {Q : State → Prop}
    (k : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → Frame [⟨sc, 8192⟩, below t.sp 48] t.mem t'.mem →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) → Repr t'.mem sc [] → Q t') :
    WP isa (hashInit sr) t Q := by
  refine WP.seq (wp_addi (imm := 0) hsr (by decide) fun u hu => WP.block_nil ?_)
  have h3 : u.gpr .r3 = sc := by rw [hu.gpr, BitVec.add_zero, hs]
  refine C.ok.callInit_ok h3 ⟨by rw [hu.sp]; exact he.sp, by rw [hu.sp]; exact he.d.sub_right (sub_sc0 sc (n := 192) (by decide))⟩
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, hu.wr, hu.rd]; exact (cov_sc0 (ws := t.rd ++ t.wr) (n := 192) (List.mem_append_right _ he.w) (by decide)))
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr, hu.wr]; exact cov_sc0 (n := 192) he.w (by decide)) fun t' h₁ h₂ h₃ hf hp hr => ?_
  refine k t' (h₁.trans hu.rd) (h₂.trans hu.wr) (h₃.trans hu.sp) ?_ (fun r hr => ?_) (by rw [C.repr] at hr; exact hr)
  · rw [← hu.mem, ← hu.sp]
    exact hf.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, sub_sc0 sc (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · rw [hp r hr, hu.other r fun e => r3_pres (e ▸ hr)]

theorem Covers.app {xs ys ws : List Region} (h₁ : Covers xs ws) (h₂ : Covers ys ws) : Covers (xs ++ ys) ws := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁ a n ⟨r, hr, hc⟩
  · exact h₂ a n ⟨r, hr, hc⟩

/-- The state and the working space, in the scratch space. -/
theorem cov_hash {ws : List Region} {sc : Addr} (hw : (⟨sc, 8192⟩ : Region) ∈ ws) :
    Covers [⟨sc, 192⟩, ⟨sc + BitVec.ofNat 64 192, 224⟩] ws :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_sc0 (n := 192) hw (by decide)
    · exact cov_sc (d := 192) (n := 224) hw (by decide)

theorem hash_disj (sc : Addr) : Region.Disjoint ⟨sc, 192⟩ ⟨sc + BitVec.ofNat 64 192, 224⟩ :=
  Offset.base_disjoint sc (by decide) (by decide)

theorem frame_hash {sc sp : Addr} {m m' : Mem}
    (h : Frame ([⟨sc, 192⟩, ⟨sc + BitVec.ofNat 64 192, 224⟩] ++ [below sp 48]) m m') :
    Frame [⟨sc, 8192⟩, below sp 48] m m' :=
  h.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_sc0 sc (by decide)⟩
    · exact ⟨_, List.mem_cons_self, sub_sc sc (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

theorem pres_args {r : Reg} (hr : r ∈ preserved) : r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 := by
  revert hr; cases r <;> decide

/-- `update` of the state at `sc` (in `sr`) with the `len` bytes at `dat` (`off(src)`), the count
set by `cnt` and the length by `ln`. -/
theorem hashUpdate_ok (C : ShaOK) {t : State} {sr src : Reg} {sc dat : Addr} {cnt ln : List Instr}
    {vc vl : (Reg → BitVec 64) → BitVec 64} {off len : Nat}
    (hsr : sr ≠ .r0) (hsr' : sr ≠ .r3 ∧ sr ≠ .r4 ∧ sr ≠ .r5 ∧ sr ≠ .r6) (hsrc : src ≠ .r0)
    (hsrc' : src ≠ .r3 ∧ src ≠ .r4) (hoff : off < 2 ^ 15)
    (hs : t.gpr sr = sc) (hd : t.gpr src + BitVec.ofNat 64 off = dat)
    (hcnt : Sets cnt .r4 vc) (hln : Sets ln .r6 vl)
    (hvc : ∀ g g' : Reg → BitVec 64, (∀ r, r ≠ .r3 → g r = g' r) → vc g = vc g')
    (hvl : ∀ g g' : Reg → BitVec 64, (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → g r = g' r) → vl g = vl g')
    (hl : (vl t.gpr).toNat = len) (he : ScEnv sc t)
    (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr)) (hdsc : Region.Disjoint ⟨dat, len⟩ ⟨sc, 8192⟩)
    (hdsp : (below t.sp 48).Disjoint ⟨dat, len⟩) {Q : State → Prop}
    (k : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → Frame [⟨sc, 8192⟩, below t.sp 48] t.mem t'.mem →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      (∀ m, Repr t.mem sc m → vc t.gpr = BitVec.ofNat 64 m.length →
        Repr t'.mem sc (m ++ Spec.Ed25519.bytesAt t.mem dat len)) → Q t') :
    WP isa (hashUpdate sr cnt src off ln) t Q := by
  unfold hashUpdate mov
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := 0) hsr (by decide) fun u₁ h₁ => hcnt _ u₁ _ fun u₂ h₂ _ =>
    wp_addi hsrc hoff fun u₃ h₃ => hln _ u₃ _ fun u₄ h₄ _ => wp_addi (imm := 192) hsr (by decide)
      fun u₅ h₅ => WP.block_nil ?_)
  obtain ⟨s3, s4, s5, s6⟩ := hsr'
  have g3 : u₅.gpr .r3 = sc := by
    rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr,
      BitVec.add_zero, hs]
  have g4 : u₅.gpr .r4 = vc t.gpr := by
    rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
    exact hvc _ _ fun r hr => h₁.other r hr
  have g5 : u₅.gpr .r5 = dat := by
    rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.other _ hsrc'.2, h₁.other _ hsrc'.1, hd]
  have g6 : (u₅.gpr .r6).toNat = len := by
    rw [h₅.other _ (by decide), h₄.gpr, ← hl]
    congr 1
    exact hvl _ _ fun r r3 r4 r5 => by rw [h₃.other r r5, h₂.other r r4, h₁.other r r3]
  have g7 : u₅.gpr .r7 = sc + BitVec.ofNat 64 192 := by
    rw [h₅.gpr, h₄.other _ s6, h₃.other _ s5, h₂.other _ s4, h₁.other _ s3, hs]
  have grd : u₅.rd = t.rd := by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  have gwr : u₅.wr = t.wr := by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  have gsp : u₅.sp = t.sp := by rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  have gm : u₅.mem = t.mem := by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have gp : ∀ r ∈ preserved, u₅.gpr r = t.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, p6, p7⟩ := pres_args hr
    rw [h₅.other _ p7, h₄.other _ p6, h₃.other _ p5, h₂.other _ p4, h₁.other _ p3]
  have hsp : 48 ≤ u₅.sp.toNat := gsp ▸ he.sp
  have hb : (below u₅.sp 48).Disjoint ⟨sc, 8192⟩ := gsp ▸ he.d
  refine C.ok.callUpd_ok g3 g5 g6 g7 (hash_disj sc) (hdsc.sub_right (sub_sc0 sc (by decide)))
    (hdsc.sub_right (sub_sc sc (by decide))) hsp (hb.sub_right (sub_sc0 sc (by decide)))
    (gsp ▸ hdsp) (hb.sub_right (sub_sc sc (by decide)))
    (by rw [grd, gwr]; exact Covers.app hdc (cov_hash (List.mem_append_right _ he.w)))
    (by rw [gwr]; exact cov_hash he.w) fun t' e₁ e₂ e₃ hf hp hr => ?_
  refine k t' (e₁.trans grd) (e₂.trans gwr) (e₃.trans gsp) (by rw [← gm, ← gsp]; exact frame_hash hf)
    (fun r hr => (hp r hr).trans (gp r hr)) fun m hm hc => ?_
  rw [C.repr] at hr
  have := hr m (by rw [gm]; exact hm) (by rw [g4]; exact hc)
  rw [gm] at this
  exact this

/-- `finalize` of the state at `sc` (in `sr`) into the 64 bytes at `o(f)`, the count set by `cnt`. -/
theorem hashFinalize_ok (C : ShaOK) {t : State} {sr f : Reg} {sc out : Addr} {cnt : List Instr}
    {vc : (Reg → BitVec 64) → BitVec 64} {o : Nat}
    (hsr : sr ≠ .r0) (hsr' : sr ≠ .r3 ∧ sr ≠ .r4 ∧ sr ≠ .r5) (hf0 : f ≠ .r0) (hf' : f ≠ .r3 ∧ f ≠ .r4)
    (ho : o < 2 ^ 15) (hs : t.gpr sr = sc) (hd : t.gpr f + BitVec.ofNat 64 o = out)
    (hcnt : Sets cnt .r4 vc) (hvc : ∀ g g' : Reg → BitVec 64, (∀ r, r ≠ .r3 → g r = g' r) → vc g = vc g')
    (he : ScEnv sc t) (hdw : Covers [⟨out, 64⟩] t.wr) (hdsc : Region.Disjoint ⟨out, 64⟩ ⟨sc, 8192⟩)
    (hdsp : (below t.sp 48).Disjoint ⟨out, 64⟩) {Q : State → Prop}
    (k : ∀ t', t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp → Frame [⟨sc, 8192⟩, ⟨out, 64⟩, below t.sp 48] t.mem t'.mem →
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      (∀ m, Repr t.mem sc m → m.length < 2 ^ 64 → vc t.gpr = BitVec.ofNat 64 m.length →
        Spec.Ed25519.bytesAt t'.mem out 64 = Spec.Sha512.sha512 m) → Q t') :
    WP isa (hashFinalize sr cnt f o) t Q := by
  unfold hashFinalize mov
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := 0) hsr (by decide) fun u₁ h₁ => hcnt _ u₁ _ fun u₂ h₂ _ =>
    wp_addi hf0 ho fun u₃ h₃ => wp_addi (imm := 192) hsr (by decide) fun u₄ h₄ => WP.block_nil ?_)
  obtain ⟨s3, s4, s5⟩ := hsr'
  have g3 : u₄.gpr .r3 = sc := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, BitVec.add_zero, hs]
  have g4 : u₄.gpr .r4 = vc t.gpr := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
    exact hvc _ _ fun r hr => h₁.other r hr
  have g5 : u₄.gpr .r5 = out := by
    rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ hf'.2, h₁.other _ hf'.1, hd]
  have g6 : u₄.gpr .r6 = sc + BitVec.ofNat 64 192 := by
    rw [h₄.gpr, h₃.other _ s5, h₂.other _ s4, h₁.other _ s3, hs]
  have grd : u₄.rd = t.rd := by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  have gwr : u₄.wr = t.wr := by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  have gsp : u₄.sp = t.sp := by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  have gm : u₄.mem = t.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have gp : ∀ r ∈ preserved, u₄.gpr r = t.gpr r := fun r hr => by
    obtain ⟨p3, p4, p5, p6, -⟩ := pres_args hr
    rw [h₄.other _ p6, h₃.other _ p5, h₂.other _ p4, h₁.other _ p3]
  have hsp : 48 ≤ u₄.sp.toNat := gsp ▸ he.sp
  have hb : (below u₄.sp 48).Disjoint ⟨sc, 8192⟩ := gsp ▸ he.d
  have hcw : Covers [⟨sc, 192⟩, ⟨out, 64⟩, ⟨sc + BitVec.ofNat 64 192, 224⟩] u₄.wr := by
    rw [gwr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_hash he.w a n ⟨_, List.mem_cons_self, hc⟩
    · exact hdw a n ⟨_, List.mem_cons_self, hc⟩
    · exact cov_hash he.w a n ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
  refine C.ok.callFin_ok g3 g5 g6 (hdsc.sub_right (sub_sc0 sc (by decide))).symm (hash_disj sc)
    (hdsc.sub_right (sub_sc sc (by decide))) hsp (hb.sub_right (sub_sc0 sc (by decide)))
    (gsp ▸ hdsp) (hb.sub_right (sub_sc sc (by decide)))
    (fun a n h => by obtain ⟨r, hr, hc⟩ := hcw a n h; exact ⟨r, List.mem_append_right _ hr, hc⟩) hcw
    fun t' e₁ e₂ e₃ hf hp hr => ?_
  refine k t' (e₁.trans grd) (e₂.trans gwr) (e₃.trans gsp) ?_
    (fun r hr => (hp r hr).trans (gp r hr)) fun m hm hl hc => ?_
  · rw [← gm, ← gsp]
    exact hf.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, sub_sc0 sc (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, sub_sc sc (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · rw [C.repr, C.fh] at hr
    exact hr m (by rw [gm]; exact hm) hl (by rw [g4]; exact hc)

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

/-- Three arguments, `r3`–`r5`, each an `addi` of a register the earlier ones do not write. -/
theorem args3_ok {t : State} {a b c : Reg} {i j k : Nat} (ha : a ≠ .r0) (hb : b ≠ .r0) (hc : c ≠ .r0)
    (hi : i < 2 ^ 15) (hj : j < 2 ^ 15) (hk : k < 2 ^ 15) (hb3 : b ≠ .r3) (hc3 : c ≠ .r3) (hc4 : c ≠ .r4)
    {Q : State → Prop}
    (K : ∀ u, ArgsKeep t u → u.gpr .r3 = t.gpr a + BitVec.ofNat 64 i → u.gpr .r4 = t.gpr b + BitVec.ofNat 64 j →
      u.gpr .r5 = t.gpr c + BitVec.ofNat 64 k → Q u) :
    WP isa (.block [.addi .r3 a i, .addi .r4 b j, .addi .r5 c k]) t Q :=
  wp_addi ha hi fun u₁ h₁ => wp_addi hb hj fun u₂ h₂ => wp_addi hc hk fun u₃ h₃ => WP.block_nil <|
    K u₃ ⟨by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.rd, h₂.rd, h₁.rd], by rw [h₃.wr, h₂.wr, h₁.wr],
      by rw [h₃.sp, h₂.sp, h₁.sp], fun r hr => by
        obtain ⟨p3, p4, p5, -, -⟩ := pres_args hr
        rw [h₃.other _ p5, h₂.other _ p4, h₁.other _ p3]⟩
      (by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr])
      (by rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ hb3])
      (by rw [h₃.gpr, h₂.other _ hc4, h₁.other _ hc3])

/-- Five arguments, `r3`–`r7`, each an `addi` of a register none of them writes. -/
theorem args5_ok {t : State} {a b c d e : Reg} {i j k l n : Nat} (ha : a ≠ .r0) (hb : b ≠ .r0) (hc : c ≠ .r0)
    (hd : d ≠ .r0) (he : e ≠ .r0) (hi : i < 2 ^ 15) (hj : j < 2 ^ 15) (hk : k < 2 ^ 15) (hl : l < 2 ^ 15)
    (hn : n < 2 ^ 15) (hs : ∀ x ∈ [b, c, d, e], x ∈ preserved) {Q : State → Prop}
    (K : ∀ u, ArgsKeep t u → u.gpr .r3 = t.gpr a + BitVec.ofNat 64 i → u.gpr .r4 = t.gpr b + BitVec.ofNat 64 j →
      u.gpr .r5 = t.gpr c + BitVec.ofNat 64 k → u.gpr .r6 = t.gpr d + BitVec.ofNat 64 l →
      u.gpr .r7 = t.gpr e + BitVec.ofNat 64 n → Q u) :
    WP isa (.block [.addi .r3 a i, .addi .r4 b j, .addi .r5 c k, .addi .r6 d l, .addi .r7 e n]) t Q := by
  have pb := pres_args (hs b (by simp))
  have pc := pres_args (hs c (by simp))
  have pd := pres_args (hs d (by simp))
  have pe := pres_args (hs e (by simp))
  exact wp_addi ha hi fun u₁ h₁ => wp_addi hb hj fun u₂ h₂ => wp_addi hc hk fun u₃ h₃ =>
    wp_addi hd hl fun u₄ h₄ => wp_addi he hn fun u₅ h₅ => WP.block_nil <|
    K u₅ ⟨by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
      by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp], fun r hr => by
        obtain ⟨p3, p4, p5, p6, p7⟩ := pres_args hr
        rw [h₅.other _ p7, h₄.other _ p6, h₃.other _ p5, h₂.other _ p4, h₁.other _ p3]⟩
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

end VG.Proof.Ed25519.PPC64LE.Whole
