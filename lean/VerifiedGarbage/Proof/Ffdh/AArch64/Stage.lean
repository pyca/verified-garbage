module

public import VerifiedGarbage.Proof.Ffdh.AArch64.SetupCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.ChecksCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.PowCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.Scan
public import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# FFDH on AArch64: the stages of a run

The domain operations share their pieces: the check of p (`domHead`), the
workspaces for p (`head`, `pSetup`), loads of numbers into the inner
workspace, the range check of a number, `R² mod p`, exponentiations, and the
moves between the workspaces. A run's data (`FD`: the working space, the
lengths, the domain, the outer header's argument slots and the other
inputs) fixes what each stage (`Base`, `E1`, `CE`, `In`, `Pa`, `Md`) says of
a state, and each piece's correctness takes a stage to the next.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A run's data. -/
structure FD where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  /-- The outer header's argument slots, and their values. -/
  hs : List (Nat × BitVec 64)
  /-- The other inputs: their pointers and octets. -/
  srcs : List (Addr × List Byte)

namespace FD

abbrev w (D : FD) : Nat := (D.k + 7) / 8

/-- p. -/
abbrev P (D : FD) : Nat := Spec.Rsa.os2ip (D.dom.take D.k)

/-- g. -/
abbrev G (D : FD) : Nat := Spec.Rsa.os2ip ((D.dom.drop D.k).take D.k)

/-- q's octets, for a domain with q. -/
abbrev qb (D : FD) : List Byte := (D.dom.drop (2 * D.k)).take D.k

/-- Whether p is a valid modulus. -/
abbrev mv (D : FD) : Bool := Spec.Rsa.modulusValid D.P D.k

/-- The front's public data. -/
abbrev d (D : FD) : DPub := ⟨D.B, D.Z, D.k, D.dp⟩

/-- The inner workspace. -/
abbrev ws (D : FD) : Ws := ⟨off D.B (inner D.w), slot D.w 8, D.w⟩

/-- The header slots after the entry. -/
abbrev hdr (D : FD) : List (Nat × BitVec 64) :=
  [(sDom, D.dp), (sDomLen, BitVec.ofNat 64 D.dl), (sK, BitVec.ofNat 64 D.k)] ++ D.hs

/-- And after `domHead`. -/
abbrev hdrQ (D : FD) : List (Nat × BitVec 64) :=
  D.hdr ++ [(sG, D.dp + BitVec.ofNat 64 D.k), (sQ, D.dp + BitVec.ofNat 64 (2 * D.k))]

end FD

/-- The registers a function keeps for its caller, all but these. -/
abbrev KX (s t : State) : Prop := Keep (.x0 :: mmRegs) s t

/-- The argument slots: none of the shared pieces writes them. -/
abbrev argSlots : List Nat := [sY, sX, sXl, VG.Impl.Ffdh.AArch64.Domain.sOut, sRand, sXe, sMsk]

/-- The slots the shared pieces keep. -/
abbrev keptSlots : List Nat := [sDom, sDomLen, sK, sG, sQ] ++ argSlots

/-- What every stage keeps. -/
structure Base (D : FD) (t : State) : Prop where
  scr : Scr t D.B D.Z
  k1 : 64 ≤ D.k
  k2 : D.k ≤ 1024
  dl : D.dl = 2 * D.k ∨ D.dl = 3 * D.k
  hZ : 128 * D.k + 256 ≤ D.Z
  dom : Src t D.B D.Z D.dp D.dom
  doml : D.dom.length = D.dl
  srcs : ∀ e ∈ D.srcs, Src t D.B D.Z e.1 e.2
  hs : ∀ q ∈ D.hs, q.1 ∈ argSlots

theorem Base.step {D : FD} {t u : State} (h : Base D t) (hi : InScr D.B D.Z t.mem u.mem) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) : Base D u :=
  ⟨h.scr.congr hwr, h.k1, h.k2, h.dl, h.hZ, h.dom.congr hi hrd hwr, h.doml,
    fun e he => (h.srcs e he).congr hi hrd hwr, h.hs⟩

theorem Base.keep {D : FD} {t u : State} (h : Base D t) (hi : InScr D.B D.Z t.mem u.mem) {rs : List Reg}
    (k : Keep rs t u) : Base D u := h.step hi k.rd k.wr

theorem Base.ew {D : FD} {t : State} (_ : Base D t) : 8 * D.w ≤ D.k + 7 ∧ D.k ≤ 8 * D.w := by
  unfold FD.w; omega_arith

theorem Base.room {D : FD} {t : State} (h : Base D t) : inner D.w + slot D.w 8 + tabBytes32 D.w ≤ D.Z :=
  room_k h.k1 h.hZ

theorem Base.w2 {D : FD} {t : State} (h : Base D t) : 2 ≤ D.w := by have := h.ew; have := h.k1; omega_arith

theorem Base.w28 {D : FD} {t : State} (h : Base D t) : D.w < 2 ^ 28 := by have := h.ew; have := h.k2; omega_arith

theorem Base.plen {D : FD} {t : State} (h : Base D t) : (D.dom.take D.k).length = D.k := by
  rw [List.length_take, h.doml]; rcases h.dl with e | e <;> omega_arith

theorem Base.qlen {D : FD} {t : State} (h : Base D t) (hq : D.dl = 3 * D.k) : D.qb.length = D.k := by
  simp only [FD.qb, List.length_take, List.length_drop, h.doml, hq]; omega_arith

theorem Base.glen {D : FD} {t : State} (h : Base D t) : ((D.dom.drop D.k).take D.k).length = D.k := by
  simp only [List.length_take, List.length_drop, h.doml]; rcases h.dl with e | e <;> omega_arith

/-! ## Slots of the outer header -/

theorem hdr_kept (D : FD) (hs : ∀ q ∈ D.hs, q.1 ∈ argSlots) : ∀ q ∈ D.hdrQ, q.1 ∈ keptSlots := by
  intro q hq
  simp only [FD.hdrQ, FD.hdr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [keptSlots, List.mem_append]
  rcases hq with ((rfl | rfl | rfl) | hq) | (rfl | rfl)
  · simp
  · simp
  · simp
  · exact Or.inr (hs q hq)
  · simp
  · simp

theorem kept_lt : ∀ i ∈ keptSlots, i < 32 := by decide

/-- A workspace's ranges (`wsMod`) miss the slots the pieces keep. -/
theorem kept_wsR (w : Nat) :
    ∀ r ∈ [(8 * sWs, 8), (inner w, slot w 8)], ∀ i ∈ keptSlots, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · decide
  · intro i hi
    have := kept_lt i hi
    have : 256 ≤ inner w := by simp only [inner, slot, hdrBytes]; omega
    exact Or.inl (by simp only; omega)

/-- The setup's ranges miss the slots the pieces keep. -/
theorem kept_setupR (w : Nat) : ∀ r ∈ setupR w, ∀ i ∈ keptSlots, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  intro r hr
  simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · intro i hi
    have := kept_lt i hi
    have : 256 ≤ inner w := by simp only [inner, slot, hdrBytes]; omega
    exact Or.inl (by simp only; omega)

theorem hdr_in (D : FD) (hs : ∀ q ∈ D.hs, q.1 ∈ argSlots) : ∀ q ∈ D.hdr, q.1 ∈ [sDom, sDomLen, sK] ++ argSlots := by
  intro q hq
  simp only [FD.hdr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl) | hq
  · simp
  · simp
  · simp
  · exact List.mem_append_right _ (hs q hq)

theorem hdr_sub (D : FD) : ∀ q ∈ D.hdr, q ∈ D.hdrQ := fun _ hq => List.mem_append_left _ hq

/-- Slots kept by a change of other ranges. -/
theorem slots_frm {D : FD} {m m' : Mem} {rs : List (Nat × Nat)} (hs : ∀ q ∈ D.hs, q.1 ∈ argSlots)
    (h : Slots m D.B D.hdrQ) (hf : Frm D.B rs m m') (hr : ∀ r ∈ rs, ∀ i ∈ keptSlots, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) :
    Slots m' D.B D.hdrQ :=
  h.frm hf (fun q hq r hr' => hr r hr' q.1 (hdr_kept D hs q hq)) fun q hq => kept_lt _ (hdr_kept D hs q hq)

/-- Slots kept when the outer header is. -/
theorem slots_eq {D : FD} {m m' : Mem} (h : Slots m D.B D.hdrQ) (hs : ∀ q ∈ D.hs, q.1 ∈ argSlots)
    (he : ∀ i < 32, word m' D.B (8 * i) = word m D.B (8 * i)) : Slots m' D.B D.hdrQ := fun q hq => by
  rw [he _ (kept_lt _ (hdr_kept D hs q hq))]; exact h q hq

theorem Slots.get {m : Mem} {B : Addr} {L : List (Nat × BitVec 64)} (h : Slots m B L) {i : Nat} {v : BitVec 64}
    (hv : (i, v) ∈ L) : word m B (8 * i) = v := by simpa only using h _ hv

/-! ## The check of p -/

/-- After the entry. -/
def E1 (D : FD) (t : State) : Prop := Base D t ∧ t.gpr .x0 = D.B ∧ Slots t.mem D.B D.hdr

theorem E1.dhp {D : FD} {t : State} (h : E1 D t) : DHP D.d t := by
  obtain ⟨hb, h0, hs⟩ := h
  have := hb.hZ
  exact ⟨hb.scr, h0, show 256 ≤ D.Z by omega_arith, hs.get (i := sDom) (v := D.dp) (by simp), hs.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp)⟩

/-- After `domHead`. -/
def CE (D : FD) (t : State) : Prop :=
  Base D t ∧ t.gpr .x0 = D.B ∧ Slots t.mem D.B D.hdrQ ∧ t.gpr .x9 = BitVec.ofNat 64 D.mv.toNat

theorem e1_ce (D : FD) (t : State) (h : E1 D t) : WP isa (.block domHead) t fun u => CE D u ∧ KX t u := by
  obtain ⟨hb, h0, hs⟩ := h
  have hn := hb.scr.nowrap
  have hZ := hb.hZ
  refine WP.mono (domHead_ok hb.scr h0 (by omega_arith) hb.k1 hb.k2 (hs.get (i := sDom) (v := D.dp) (by simp)) (hs.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp))
    (hb.dom.take D.k) hb.plen) fun u ⟨h9, hG, hQ, f, h0', k⟩ => ⟨⟨hb.keep (InScr.of_frm f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sG, sQ, sFn] <;> omega_arith) k, h0', ?_, h9⟩, k.mono (by decide)⟩
  have hs' : Slots u.mem D.B D.hdr := hs.frm f (fun q hq r hr => by
      have hk := hdr_in D hb.hs q hq
      simp only [argSlots, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        rcases hk with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide)
    (fun q hq => kept_lt _ (hdr_kept D hb.hs q (hdr_sub D q hq)))
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hs' q hq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hG
    · exact hQ

theorem ce_eval {D : FD} {t : State} (h : CE D t) :
    isa.eval (.zero .x .x9) t = some (BitVec.ofNat 64 D.mv.toNat == 0) := by
  rw [eval_zero, h.2.2.2]

theorem ce_valid {D : FD} {t : State} (h : CE D t) (he : isa.eval (.zero .x .x9) t = some false) : D.mv = true := by
  rw [ce_eval h] at he
  cases hv : D.mv
  · rw [hv] at he; simp at he
  · rfl

theorem ce_setupP (D : FD) (t : State) (h : CE D t) (he : isa.eval (.zero .x .x9) t = some false) :
    SetupP D.d t := by
  have hv := ce_valid h he
  obtain ⟨hb, h0, hs, -⟩ := h
  obtain ⟨hodd, -⟩ := valid_facts hv hb.k1
  exact ⟨D.dom.take D.k, hb.scr, h0, hb.k1, hb.k2, hb.hZ, hs.get (i := sDom) (v := D.dp) (by simp), hs.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp), hb.dom.take D.k,
    hb.plen, hodd⟩

/-! ## The inner workspace -/

/-- In the inner workspace for p, with what the outer one keeps. -/
def In (D : FD) (mi : BitVec 64) (t : State) : Prop :=
  Base D t ∧ SubCtx t D.B D.Z (inner D.w) D.w D.w mi ∧ XVals t D.B (inner D.w) D.w mi D.P ∧
    word t.mem D.B (8 * sWs) = off D.B (inner D.w) ∧ Slots t.mem D.B D.hdrQ ∧ D.mv = true

theorem ce_in (D : FD) (t : State) (h : CE D t) (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (seqs (([.block head] : List (Prog isa)) ++ pSetup)) t fun u => (∃ mi, In D mi u) ∧ KX t u := by
  have hv := ce_valid h he
  obtain ⟨hb, h0, hs, -⟩ := h
  have hn := hb.scr.nowrap
  have hroom := hb.room
  obtain ⟨hodd, -⟩ := valid_facts hv hb.k1
  have hi256 : 256 ≤ inner D.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega_arith
  have h8 := hdr_lt_slot D.w 8 (show 31 < 32 by decide)
  refine WP.mono (setup_ok hb.scr h0 hb.k1 hb.k2 hb.hZ (hs.get (i := sDom) (v := D.dp) (by simp)) (hs.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp)) (hb.dom.take D.k)
    hb.plen hodd) fun u ⟨mi, hc, hX, hWs, f, k⟩ => ?_
  rw [show (D.k + 7) / 8 = D.w from rfl] at f
  refine ⟨⟨mi, hb.keep (InScr.of_frm f fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, sWs, sFn] <;> omega_arith) k,
      hc, hX, hWs, slots_frm hb.hs hs f (kept_setupR D.w), hv⟩, k⟩

theorem In.step {D : FD} {mi : BitVec 64} {t u : State} (h : In D mi t) {rs : List (Nat × Nat)}
    (hf : Frm (off D.B (inner D.w)) rs t.mem u.mem) (hr : ∀ r ∈ rs, StepR D.w r) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) (h0 : u.gpr .x0 = t.gpr .x0) : In D mi u := by
  obtain ⟨hb, hc, hv, hWs, hs, hm⟩ := h
  have hroom := hb.room
  have ew := hb.ew
  have := hb.k1
  have hGn := hc.good.scr.nowrap
  have hc' := hc.of_frm hf (fun r hr' => ⟨(hr r hr').1, (hr r hr').2.1⟩) hwr h0
  obtain ⟨hbw, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega_arith) hf (fun r hr' => by
    have := (hr r hr').2.1; omega_arith)
  exact ⟨hb.step hi hrd hwr, hc', hv.of_frmA hGn (by omega_arith) hf (fun r hr' => (hr r hr').2.2),
    by rw [hbw _ (by decide)]; exact hWs, slots_eq hs hb.hs hbw, hm⟩

theorem In.keep {D : FD} {mi : BitVec 64} {t u : State} (h : In D mi t) (hm : u.mem = t.mem) {rs : List Reg}
    (k : Keep rs t u) (h0 : .x0 ∉ rs) : In D mi u :=
  h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (fun _ h => absurd h List.not_mem_nil) k.rd k.wr
    (k.gpr .x0 h0)

theorem In.goodW1 {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) : GoodW1 D.ws t := by
  obtain ⟨hb, hc, -⟩ := h
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  exact ⟨⟨mi, hc.good, Nat.le_refl _⟩, show 1 ≤ D.w by omega_arith, show D.w < 2 ^ 31 by omega_arith⟩

/-- A load's public data. -/
abbrev FD.ld (D : FD) (ptr : Addr) (len : Nat) : BPub := ⟨⟨D.B, D.Z, inner D.w, D.w, D.w⟩, ptr, len⟩

/-- `loadArr j sp sl`'s hypotheses. -/
theorem In.lpre {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) {j sp sl : Nat} (hj : j < 8)
    (hsp : sp < 32) (hsl : sl < 32) {ptr : Addr} {bs : List Byte} (hp : word t.mem D.B (8 * sp) = ptr)
    (hl : word t.mem D.B (8 * sl) = BitVec.ofNat 64 bs.length) (hsrc : Src t D.B D.Z ptr bs) (h1 : 1 ≤ bs.length)
    (hkw : bs.length ≤ D.k) : LPre j sp sl (D.ld ptr bs.length) t := by
  obtain ⟨hb, hc, -⟩ := h
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  exact ⟨mi, bs, hc, show 2 ≤ D.w by omega_arith, Nat.le_refl _, show D.w < 2 ^ 30 by omega_arith, hj, hsp, hsl, hp, hl, rfl, hsrc,
    h1, by omega_arith, show (bs.length + 7) / 8 ≤ D.w by omega_arith⟩

/-- `loadArr j sp sl`. -/
theorem In.load {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) {j sp sl : Nat} (hj : j < 8) (hjN : j ≠ aN)
    (hjO : j ≠ aOne) (hsp : sp < 32) (hsl : sl < 32) {ptr : Addr} {bs : List Byte}
    (hp : word t.mem D.B (8 * sp) = ptr) (hl : word t.mem D.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src t D.B D.Z ptr bs) (h1 : 1 ≤ bs.length) (hkw : bs.length ≤ D.k) :
    WP isa (seqs (Crt.loadArr j sp sl)) t fun u =>
      (In D mi u ∧ wv u.mem (off D.B (inner D.w)) (slot D.w j) D.w = Spec.Rsa.os2ip bs ∧
        Outside (off D.B (inner D.w)) (slot D.w j) (8 * (D.w + 2)) t.mem u.mem) ∧ KX t u := by
  have ew := h.1.ew
  have := h.1.k1
  have := h.1.k2
  refine WP.mono (primeLoad_ok h.2.1 (show 2 ≤ D.w by omega_arith) (Nat.le_refl _) (show D.w < 2 ^ 30 by omega_arith) hj hsp hsl
    hp hl hsrc h1 (by omega_arith) (show (bs.length + 7) / 8 ≤ D.w by omega_arith))
    fun u ⟨_, hy, ho, k⟩ => ⟨⟨h.step (rs := [(slot D.w j, 8 * (D.w + 2))]) (Frm.of_outside ho (by simp))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact stepR_arr _ hj hjN hjO) k.rd k.wr
      (k.gpr .x0 (by decide)), hy, ho⟩, k.mono (by decide)⟩

/-- `range a`. -/
theorem In.range {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) :
    WP isa (seqs (range a)) t fun u => (In D mi u ∧
      u.gpr .x9 = bit (1 < wv t.mem (off D.B (inner D.w)) (slot D.w a) D.w ∧
        2 * (wv t.mem (off D.B (inner D.w)) (slot D.w a) D.w / 2) + 1 < D.P) ∧
      word u.mem (off D.B (inner D.w)) (8 * sF) = u.gpr .x9 ∧
      Frm (off D.B (inner D.w)) [(slot D.w aTmp, 8 * D.w), (8 * sF, 8)] t.mem u.mem) ∧ KX t u := by
  have h' := h
  obtain ⟨hb, hc, hv, -⟩ := h'
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  refine WP.mono (range_ok hc.good (Nat.le_refl _) (show 1 ≤ D.w by omega_arith) (show D.w < 2 ^ 31 by omega_arith) ha haT
    hv.one) fun u ⟨h9, hF, f, k⟩ => ⟨⟨h.step f (fun r hr => ?_) k.rd k.wr (k.gpr .x0 (by decide)),
      by rw [h9, hv.n], hF, f⟩, k.mono (by decide)⟩
  have := slot_le (w := D.w) (show aTmp < 8 by decide)
  have := hdr_lt_slot D.w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot D.w 8 (show sF < 32 by decide)
  have := hdr_lt_slot D.w aN (show sF < 32 by decide)
  have := hdr_lt_slot D.w aOne (show sF < 32 by decide)
  have s1 := slot_sep (w := D.w) (show aTmp ≠ aN by decide)
  have s2 := slot_sep (w := D.w) (show aTmp ≠ aOne by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [sF, sFn] at * <;> omega_arith

/-! ## The outer workspace -/

/-- Back in the outer workspace, the inner one kept. -/
def Pa (D : FD) (mi : BitVec 64) (t : State) : Prop :=
  Base D t ∧ SubMem t D.B D.Z (inner D.w) D.w D.w mi ∧ XVals t D.B (inner D.w) D.w mi D.P ∧
    word t.mem D.B (8 * sWs) = off D.B (inner D.w) ∧ Slots t.mem D.B D.hdrQ ∧ D.mv = true ∧ t.gpr .x0 = D.B

theorem In.pa {D : FD} {mi : BitVec 64} {t u : State} (h : In D mi t) (hm : u.mem = t.mem) {rs : List Reg}
    (k : Keep rs t u) (h0 : u.gpr .x0 = D.B) : Pa D mi u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv⟩ := h
  exact ⟨hb.keep (by rw [hm]; exact InScr.refl _ _ _) k, hc.toMem.congr hm k.wr,
    ⟨by rw [hm]; exact hv.n, by rw [hm]; exact hv.inv, by rw [hm]; exact hv.one⟩, by rw [hm]; exact hWs,
    by rw [hm]; exact hs, hmv, h0⟩

theorem Pa.outer {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) : Outer t D.B D.Z D.w :=
  Outer.of_mem h.2.1 h.2.2.2.2.2.2 h.1.room h.1.w2 h.1.w28

theorem In.leave {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    WP isa (.block [Crt.leave]) t fun u => Pa D mi u ∧ KX t u :=
  WP.mono (leave_ok h.2.1) fun _ ⟨⟨h0, hm⟩, k⟩ => ⟨h.pa hm k h0, k.mono (by decide)⟩

theorem In.leaveQ {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    WP isa (.block (Crt.leave :: qTest)) t fun u => (Pa D mi u ∧ u.gpr .x3 = BitVec.ofNat 64 (D.dl - 2 * D.k)) ∧
      KX t u := by
  have hb := h.1
  refine WP.mono (leaveQ_ok h.2.1 (h.2.2.2.2.1.get (i := sDomLen) (v := BitVec.ofNat 64 D.dl) (by simp))
    (h.2.2.2.2.1.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp))
    (by rw [← hb.doml]; rcases hb.dl with e | e <;> rw [hb.doml] <;> omega_arith)) fun u ⟨⟨h0, h3, hm⟩, k⟩ =>
    ⟨⟨h.pa hm k h0, h3⟩, k.mono (by decide)⟩

theorem Pa.enter {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (.block [enter]) t fun u => In D mi u ∧ KX t u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv, h0⟩ := id h
  refine WP.mono (enter_ok h.outer hWs) fun u ⟨⟨h0', hm⟩, k⟩ =>
    ⟨⟨hb.keep (by rw [hm]; exact InScr.refl _ _ _) k, (hc.congr hm k.wr).ctx h0',
      ⟨by rw [hm]; exact hv.n, by rw [hm]; exact hv.inv, by rw [hm]; exact hv.one⟩, by rw [hm]; exact hWs,
      by rw [hm]; exact hs, hmv⟩, k.mono (by decide)⟩

theorem Pa.enterM {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (.block [VG.Impl.Ffdh.AArch64.Domain.enter]) t fun u => (In D mi u ∧ u.mem = t.mem) ∧ KX t u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv, h0⟩ := id h
  refine WP.mono (enter_ok h.outer hWs) fun u ⟨⟨h0', hm⟩, k⟩ =>
    ⟨⟨⟨hb.keep (by rw [hm]; exact InScr.refl _ _ _) k, (hc.congr hm k.wr).ctx h0',
      ⟨by rw [hm]; exact hv.n, by rw [hm]; exact hv.inv, by rw [hm]; exact hv.one⟩, by rw [hm]; exact hWs,
      by rw [hm]; exact hs, hmv⟩, hm⟩, k.mono (by decide)⟩

theorem pa_eval3 {D : FD} {t : State} (h3 : t.gpr .x3 = BitVec.ofNat 64 (D.dl - 2 * D.k)) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) := by
  rw [eval_zero, h3]

theorem Base.q {D : FD} {t : State} (hb : Base D t) (he : (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) = false) :
    D.dl = 3 * D.k := by
  have := hb.k2
  rcases hb.dl with hd | hd
  · rw [hd, show 2 * D.k - 2 * D.k = 0 by omega_arith] at he; simp at he
  · exact hd

theorem Base.noq {D : FD} {t : State} (hb : Base D t) (he : (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) = true) :
    D.dl = 2 * D.k := by
  have := hb.k2
  rcases hb.dl with hd | hd
  · exact hd
  · rw [hd, show 3 * D.k - 2 * D.k = D.k by omega_arith] at he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (show D.k < 2 ^ 64 by omega_arith)] at this
    have : D.k = 0 := this
    have := hb.k1
    omega_arith

/-- q's octets and their pointer. -/
abbrev FD.qs (D : FD) : ScanPub := ⟨D.B, D.Z, D.w, D.dp + BitVec.ofNat 64 (2 * D.k), D.qb⟩

/-- The source of q. -/
theorem Base.qsrc {D : FD} {t : State} (hb : Base D t) :
    Src t D.B D.Z (D.dp + BitVec.ofNat 64 (2 * D.k)) D.qb :=
  (hb.dom.drop (2 * D.k)).take D.k

/-- The source of g. -/
theorem Base.gsrc {D : FD} {t : State} (hb : Base D t) :
    Src t D.B D.Z (D.dp + BitVec.ofNat 64 D.k) ((D.dom.drop D.k).take D.k) :=
  (hb.dom.drop D.k).take D.k

/-- `scan sQ`'s hypotheses. -/
theorem Pa.scanPre {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) (hq : D.dl = 3 * D.k) :
    ScanPre sQ D.qs t := by
  have hb := h.1
  have hs := h.2.2.2.2.1
  have hl := hb.qlen hq
  have := hb.k1
  have := hb.k2
  show Outer t D.B D.Z D.w ∧ word t.mem D.B (8 * sQ) = D.dp + BitVec.ofNat 64 (2 * D.k) ∧
    word t.mem D.B (8 * sK) = BitVec.ofNat 64 D.qb.length ∧ D.qb ≠ [] ∧ D.qb.length < 2 ^ 32 ∧
    Src t D.B D.Z (D.dp + BitVec.ofNat 64 (2 * D.k)) D.qb ∧ sQ < 32
  exact ⟨h.outer, hs.get (by simp), by rw [hl]; exact hs.get (i := sK) (by simp),
    fun he' => by rw [he'] at hl; simp at hl; omega_arith, by omega_arith, hb.qsrc, by decide⟩

/-- After the scan of q. -/
def Sc (D : FD) (mi : BitVec 64) (t : State) : Prop :=
  Pa D mi t ∧ word t.mem D.B (8 * sEp) = off (D.dp + BitVec.ofNat 64 (2 * D.k)) (lead D.qb) ∧
    word t.mem D.B (8 * sEl) = BitVec.ofNat 64 (D.k - lead D.qb)

/-- `Pa` and slots after a change of the outer header's slots `sEp` and `sEl`. -/
theorem Pa.hdr {D : FD} {mi : BitVec 64} {t u : State} (h : Pa D mi t)
    (hf : Frm D.B [(8 * sEp, 8), (8 * sEl, 8)] t.mem u.mem) {rs : List Reg} (k : Keep rs t u)
    (h0 : u.gpr .x0 = D.B) : Pa D mi u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv, -⟩ := h
  have hr : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [sEp, sEl, sFn] <;> omega_arith
  have hroom := hb.room
  have hi256 : 256 ≤ inner D.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega_arith
  have i : InScr D.B D.Z t.mem u.mem := InScr.of_frm hf fun r hr' => by have := (hr r hr').2; omega_arith
  exact ⟨hb.keep i k, hc.of_parent hf hr k.wr, hv.of_parent hc hf (fun r hr' => (hr r hr').2),
    by rw [hf.word_eq (by decide) (by decide)]; exact hWs,
    slots_frm hb.hs hs hf (by decide), hmv, h0⟩

theorem Pa.scan {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) (hq : D.dl = 3 * D.k) :
    WP isa (seqs (scan sQ)) t fun u => (Sc D mi u ∧ Frm D.B [(8 * sEp, 8), (8 * sEl, 8)] t.mem u.mem) ∧
      KX t u := by
  obtain ⟨hO, hp, hk, hne, hlt, hsrc, -⟩ := (h.scanPre hq :
    Outer t D.B D.Z D.w ∧ word t.mem D.B (8 * sQ) = D.dp + BitVec.ofNat 64 (2 * D.k) ∧
    word t.mem D.B (8 * sK) = BitVec.ofNat 64 D.qb.length ∧ D.qb ≠ [] ∧ D.qb.length < 2 ^ 32 ∧
    Src t D.B D.Z (D.dp + BitVec.ofNat 64 (2 * D.k)) D.qb ∧ sQ < 32)
  have hl := h.1.qlen hq
  exact WP.mono (scan_ok hO (show sQ < 32 by decide) hp hk hne hlt hsrc) fun u ⟨hEp, hEl, _, f, k⟩ =>
    ⟨⟨⟨h.hdr f k ((k.gpr .x0 (by decide)).trans h.2.2.2.2.2.2), hEp, by rw [hEl, hl]⟩, f⟩, k.mono (by decide)⟩

/-- A change of an inner workspace of `wx` words keeps the outer workspace below
it. -/
theorem child_frm' {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (hc : SubCtx s B Z o w wx mi) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ slot wx 8 + tabBytes wx) :
    (∀ d, d + 8 ≤ o → word t.mem B d = word s.mem B d) ∧ InScr B Z s.mem t.mem := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hhi := hc.hi
  have hL : o + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64 := by omega_arith
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  refine ⟨fun d hd => hf.word_below hr hL (by omega_arith) hd, ?_⟩
  refine InScr.of_frm (hf.rebase (by omega_arith) fun r hr' => by have := hr r hr'; omega_arith) fun r hr' => ?_
  simp only [shiftRanges, List.mem_map] at hr'
  obtain ⟨r', hr'', rfl⟩ := hr'
  have := hr r' hr''
  simp only
  omega_arith

/-! ## `R² mod p` -/

/-- With `R² mod p`. -/
def Md (D : FD) (mi : BitVec 64) (t : State) : Prop :=
  Base D t ∧ ModCtx t D.B D.Z (inner D.w) D.w mi D.P ∧ word t.mem D.B (8 * sWs) = off D.B (inner D.w) ∧
    Slots t.mem D.B D.hdrQ ∧ D.mv = true

/-- `r2_ok`'s hypotheses, for the run's `-p⁻¹`. -/
theorem In.r2pre {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    R2Pre ⟨⟨off D.B (inner D.w), slot D.w 8, D.w, mi⟩, D.P⟩ t := by
  obtain ⟨hb, hc, hv, -, -, hm⟩ := h
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  obtain ⟨hodd, -, hlo⟩ := valid_facts hm hb.k1
  exact ⟨⟨hc.good, Nat.le_refl _⟩, show 2 ≤ D.w by omega_arith, show D.w < 2 ^ 30 by omega_arith, hv.n, hv.inv, hodd, hlo⟩

/-- `-p⁻¹` is the same in runs with the same p. -/
theorem In.minv {D : FD} {mi₁ mi₂ : BitVec 64} {s t : State} (h₁ : In D mi₁ s) (h₂ : In D mi₂ t) : mi₁ = mi₂ := by
  have hb := h₁.1
  have ew := hb.ew
  have := hb.k1
  obtain ⟨hodd, -⟩ := valid_facts h₁.2.2.2.2.2 hb.k1
  exact xvals_minv (show 1 ≤ D.w by omega_arith) hodd h₁.2.2.1 h₂.2.2.1

theorem In.r2 (M : Mont) {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    WP isa (seqs (r2Steps M.mm)) t fun u => (Md D mi u ∧ ∀ i < 32, word u.mem D.B (8 * i) = word t.mem D.B (8 * i)) ∧
      KX t u := by
  obtain ⟨hb, hc, hv, hWs, hs, hm⟩ := h
  have hroom := hb.room
  refine WP.mono (r2_ctx M hc hv hm hb.k1 hb.k2 hb.hZ) fun u ⟨hM, f, k⟩ => ?_
  obtain ⟨hbw, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega_arith) f (fun r hr => by
    have := r2Ranges_le D.w r hr; unfold tabBytes32; omega_arith)
  exact ⟨⟨⟨hb.keep hi k, hM, by rw [hbw _ (by decide)]; exact hWs, slots_eq hs hb.hs hbw, hm⟩, hbw⟩, k.mono (by decide)⟩

theorem Md.inn {D : FD} {mi : BitVec 64} {t : State} (h : Md D mi t) : In D mi t :=
  let ⟨hb, hM, hWs, hs, hv⟩ := h
  ⟨hb, hM.sub, hM.xv, hWs, hs, hv⟩

/-! ## Exponentiations -/

/-- An exponentiation's public data, for the base's and the exponent's pointers
and lengths. -/
abbrev FD.pw (D : FD) (pb : Addr) (lb : Nat) (pe : Addr) (le : Nat) : PowPub :=
  ⟨⟨D.B, D.Z, inner D.w, D.w, D.w⟩, pb, lb, pe, le⟩

theorem Md.ps0 {D : FD} {mi : BitVec 64} {t : State} (h : Md D mi t) {bp bl ep el : Nat} (hbp : bp < 32)
    (hbl : bl < 32) (hep : ep < 32) (hel : el < 32) {pb pe : Addr} {bb eb : List Byte}
    (hpb : word t.mem D.B (8 * bp) = pb) (hlb : word t.mem D.B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src t D.B D.Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ D.k)
    (hpe : word t.mem D.B (8 * ep) = pe) (hle : word t.mem D.B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src t D.B D.Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    PS0 bp bl ep el (D.pw pb bb.length pe eb.length) t := by
  have ew := h.1.ew
  exact ps0_of h.2.1 hbp hbl hep hel hpb hlb hsb hb1 (show (bb.length + 7) / 8 ≤ D.w by omega_arith) hpe hle hse he1 he2

theorem Md.pow (W : Window) (M : Mont) (S : Selector) {D : FD} {mi : BitVec 64} {t : State} (h : Md D mi t)
    {bp bl ep el : Nat} (hbp : bp < 32) (hbl : bl < 32) (hep : ep < 32) (hel : el < 32) {pb pe : Addr}
    {bb eb : List Byte}
    (hpb : word t.mem D.B (8 * bp) = pb) (hlb : word t.mem D.B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src t D.B D.Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ D.k)
    (hpe : word t.mem D.B (8 * ep) = pe) (hle : word t.mem D.B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src t D.B D.Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (seqs (pow W.code S.code M.mm bp bl ep el)) t fun u => Md D mi u ∧
      wv u.mem (off D.B (inner D.w)) (slot D.w aY) D.w = Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % D.P ∧
      (∀ i < 32, word u.mem D.B (8 * i) = word t.mem D.B (8 * i)) ∧ KX t u := by
  obtain ⟨hb, hM, hWs, hs, hv⟩ := h
  have ew := hb.ew
  refine WP.mono (pow_ok W M S hM hbp hbl hep hel hpb hlb hsb hb1 (show (bb.length + 7) / 8 ≤ D.w by omega_arith) hpe hle
    hse he1 he2) fun u ⟨hM', hY, f, k⟩ => ?_
  obtain ⟨hbw, hi⟩ := child_frm hM.sub hM.wide f (fun r hr => (powRanges_ok D.w r hr).2)
  exact ⟨⟨hb.keep hi k, hM', by rw [hbw _ (by decide)]; exact hWs, slots_eq hs hb.hs hbw, hv⟩, hY, hbw, k.mono (by decide)⟩

/-! ## A modulus' workspace from the outer one -/

/-- In the outer workspace, whatever the inner one holds. -/
def Ou (D : FD) (t : State) : Prop :=
  Base D t ∧ Outer t D.B D.Z D.w ∧ Slots t.mem D.B D.hdrQ ∧ D.mv = true

theorem Pa.ou {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) : Ou D t :=
  ⟨h.1, h.outer, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- The workspace of a modulus of `bs`, whose pointer and length are in the
outer slots `sp` and `sl`. -/
theorem Ou.wsMod {D : FD} {t : State} (h : Ou D t) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32)
    (hspW : sp ≠ sWs) (hslW : sl ≠ sWs) {ptr : Addr} {bs : List Byte} (hp : word t.mem D.B (8 * sp) = ptr)
    (hl : word t.mem D.B (8 * sl) = BitVec.ofNat 64 bs.length) (hsrc : Src t D.B D.Z ptr bs) (h1 : 1 ≤ bs.length)
    (hk : bs.length ≤ D.k) (hodd : Spec.Rsa.os2ip bs % 2 = 1) :
    WP isa (seqs (([.block (wsSetup sl ++ [enter])] : List (Prog isa)) ++ modSetup sp sl)) t fun u => ∃ mi,
      Base D u ∧ SubCtx u D.B D.Z (inner D.w) D.w (wsWords bs.length) mi ∧
      XVals u D.B (inner D.w) (wsWords bs.length) mi (Spec.Rsa.os2ip bs) ∧
      word u.mem D.B (8 * sWs) = off D.B (inner D.w) ∧
      Frm D.B [(8 * sWs, 8), (inner D.w, slot D.w 8)] t.mem u.mem ∧ Keep (.x0 :: mmRegs) t u := by
  obtain ⟨hb, hO, hs, hv⟩ := h
  have hn := hb.scr.nowrap
  have hroom := hO.room
  have ew := hb.ew
  have hw28 := hO.w28
  have h8 := hdr_lt_slot D.w 8 (show 31 < 32 by decide)
  have hi8 : 8 * 32 ≤ inner D.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega_arith
  have eWs : sWs = 29 := rfl
  have hwx : wsWords bs.length ≤ D.w := by unfold wsWords; have := hb.w2; omega_arith
  have hwx2 : 2 ≤ wsWords bs.length := by unfold wsWords; omega_arith
  refine wp_seqs_cons (by simp [modSetup, Crt.loadArr]) (WP.mono (wsSetup_ok (len := bs.length) hO hsl hslW hl h1
    (by omega_arith)) fun s₂ ⟨hc₂, hWs₂, f₂, k₂⟩ => ?_)
  have hb₂ : ∀ i < 32, i ≠ sWs → word s₂.mem D.B (8 * i) = word t.mem D.B (8 * i) := fun i hi hne =>
    f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have i₂ : InScr D.B D.Z t.mem s₂.mem := InScr.of_frm f₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  refine WP.mono (modSetup_ok hc₂ hwx2 hwx (by omega_arith) hsp hsl (by rw [hb₂ _ hsp hspW]; exact hp)
    (by rw [hb₂ _ hsl hslW]; exact hl) (hsrc.congrK i₂ k₂) h1 (by unfold wsWords; omega_arith) hodd)
    fun u ⟨mi, hc, hX, f₃, k₃⟩ => ?_
  have hr₃ : ∀ r ∈ [(slot (wsWords bs.length) aN, 8 * (wsWords bs.length + 2)),
      (slot (wsWords bs.length) aOne, 8 * (wsWords bs.length + 2)), (8 * sMinv, 8)],
      r.1 + r.2 ≤ slot (wsWords bs.length) 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact slot_le (by decide)
    · exact slot_le (by decide)
    · have := hdr_lt_slot (wsWords bs.length) 8 (show sMinv < 32 by decide); simp only; omega_arith
  have hs8 : slot (wsWords bs.length) 8 ≤ slot D.w 8 := by unfold slot hdrBytes; omega_arith
  have hr₃' : ∀ r ∈ [(slot (wsWords bs.length) aN, 8 * (wsWords bs.length + 2)),
      (slot (wsWords bs.length) aOne, 8 * (wsWords bs.length + 2)), (8 * sMinv, 8)],
      inner D.w + r.1 + r.2 ≤ 2 ^ 64 := fun r hr => by have := hr₃ r hr; omega_arith
  have g₃ := f₃.rebase (by omega_arith) hr₃'
  have f : Frm D.B [(8 * sWs, 8), (inner D.w, slot D.w 8)] t.mem u.mem := by
    intro x hx
    rw [g₃ x (fun r hr => by
      simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hx' := hx (inner D.w, slot D.w 8) (by simp)
      have s1 := slot_le (w := wsWords bs.length) (show aN < 8 by decide)
      have s2 := slot_le (w := wsWords bs.length) (show aOne < 8 by decide)
      have s3 := hdr_lt_slot (wsWords bs.length) 8 (show sMinv < 32 by decide)
      rcases hr with rfl | rfl | rfl <;> simp only at hx' ⊢ <;> omega_arith), f₂ x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hx (8 * sWs, 8) (by simp)
      · have hx' := hx (inner D.w, slot D.w 8) (by simp)
        simp only at hx' ⊢; omega_arith)]
  have i : InScr D.B D.Z t.mem u.mem := InScr.of_frm f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  have hWs : word u.mem D.B (8 * sWs) = off D.B (inner D.w) := by
    rw [g₃.word_eq (fun r hr => by
      simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)]
    exact hWs₂
  exact ⟨mi, hb.keep i (k₂.trans k₃), hc, hX, hWs, f, keep_trans (k₂.mono (by decide)) (k₃.mono (by decide))⟩

/-- `Pa` after a change of the outer workspace's arrays. -/
theorem Pa.outside {D : FD} {mi : BitVec 64} {t u : State} (h : Pa D mi t) {o n : Nat} (ho : 256 ≤ o)
    (hon : o + n ≤ inner D.w) (hout : Outside D.B o n t.mem u.mem) (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (h0 : u.gpr .x0 = D.B) : Pa D mi u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv, -⟩ := h
  have hn := hb.scr.nowrap
  have hroom := hb.room
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega_arith
  have hlo := hc.lo
  have hhi := hc.hi
  have hW : ∀ d, d + 8 ≤ 256 → word u.mem D.B d = word t.mem D.B d := fun d hd =>
    hout.word (Or.inl (by omega_arith)) (by omega_arith)
  have hI : ∀ d, d + 8 ≤ slot D.w 8 + tabBytes D.w →
      word u.mem (off D.B (inner D.w)) d = word t.mem (off D.B (inner D.w)) d := fun d hd => by
    rw [word_off, word_off]; exact hout.word (Or.inr (by omega_arith)) (by omega_arith)
  have hV : ∀ d k, d + 8 * k ≤ slot D.w 8 → wv u.mem (off D.B (inner D.w)) d k = wv t.mem (off D.B (inner D.w)) d k :=
    fun d k hd => by rw [wv_off, wv_off]; exact hout.wv (Or.inr (by omega_arith)) (by omega_arith)
  have sN := slot_le (w := D.w) (show aN < 8 by decide)
  have sO := slot_le (w := D.w) (show aOne < 8 by decide)
  have hN0 := hdr_lt_slot D.w aN (show 31 < 32 by decide)
  have h8 := hdr_lt_slot D.w 8 (show 31 < 32 by decide)
  refine ⟨hb.step (InScr.of_outside hout (by omega_arith)) hrd hwr,
    ⟨hc.scr.congr hwr, ⟨(hI _ (by have := hdr_lt_slot D.w 8 (show sW < 32 by decide); omega_arith)).trans hc.hdr.hw,
      (hI _ (by have := hdr_lt_slot D.w 8 (show sMinv < 32 by decide); omega_arith)).trans hc.hdr.hminv,
      fun j hj => (hI _ (by have := hdr_lt_slot D.w 8 (sArr_lt hj); omega_arith)).trans (hc.hdr.harr j hj)⟩,
      (hI _ (by have := hdr_lt_slot D.w 8 (show Crt.sLink < 32 by decide); omega_arith)).trans hc.link,
      (hW _ (by decide)).trans hc.nw, fun j hj => (hW _ (by unfold sArr; omega_arith)).trans (hc.narr j hj), hlo, hhi⟩,
    ⟨(hV _ D.w (by omega_arith)).trans hv.n, by rw [hI _ (by omega_arith)]; exact hv.inv, (hV _ D.w (by omega_arith)).trans hv.one⟩,
    (hW _ (by decide)).trans hWs, fun q hq => by
      rw [hW _ (by have := kept_lt _ (hdr_kept D hb.hs q hq); omega_arith)]; exact hs q hq, hmv, h0⟩

/-! ## Moves between the workspaces with `R² mod p` -/

/-- `R² mod p` in the inner workspace. -/
def R2f (D : FD) (t : State) : Prop :=
  wv t.mem (off D.B (inner D.w)) (slot D.w aR2) D.w < D.P ∧
    wv t.mem (off D.B (inner D.w)) (slot D.w aR2) D.w % D.P = 2 ^ (64 * D.w) * 2 ^ (64 * D.w) % D.P

theorem Md.r2f {D : FD} {mi : BitVec 64} {t : State} (h : Md D mi t) : R2f D t :=
  ⟨h.2.1.r2l, h.2.1.r2⟩

theorem In.md {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) (hr : R2f D t) : Md D mi t := by
  obtain ⟨hb, hc, hv, hWs, hs, hm⟩ := h
  obtain ⟨hodd, h1, -⟩ := valid_facts hm hb.k1
  have hroom := hb.room
  exact ⟨hb, ⟨hc, hv, hr.1, hr.2, hodd, h1, by unfold inner at hroom ⊢; omega_arith, hb.w2, hb.w28⟩, hWs, hs, hm⟩

theorem R2f.mem {D : FD} {t u : State} (h : R2f D t) (hm : u.mem = t.mem) : R2f D u := by
  unfold R2f; rw [hm]; exact h

/-- `R² mod p` after a change of the outer header. -/
theorem R2f.hdr {D : FD} {t u : State} (h : R2f D t) (hb : Base D t) {rs : List (Nat × Nat)}
    (hf : Frm D.B rs t.mem u.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ 256) : R2f D u := by
  have hn := hb.scr.nowrap
  have hroom := hb.room
  have h256 : 256 ≤ inner D.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have sR := slot_le (w := D.w) (show aR2 < 8 by decide)
  have e : wv u.mem (off D.B (inner D.w)) (slot D.w aR2) D.w = wv t.mem (off D.B (inner D.w)) (slot D.w aR2) D.w := by
    rw [wv_off, wv_off]
    exact hf.wv_eq (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by unfold tabBytes32 at hroom; omega_arith)
  unfold R2f; rw [e]; exact h

/-- The test of the domain's length, in the outer workspace. -/
theorem Pa.qtest {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (.block qTest) t fun u => (u.gpr .x3 = BitVec.ofNat 64 (D.dl - 2 * D.k) ∧ u.mem = t.mem) ∧
      Keep [.x3, .x4] t u := by
  have hO := h.outer
  have hs := h.2.2.2.2.1
  have hb := h.1
  refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  unfold VG.Impl.Ffdh.AArch64.Domain.qTest
  brun [hO.x0, hdr_enc (show sDomLen < 32 by decide), hdr_enc (show sK < 32 by decide),
    hO.ld (show sDomLen < 32 by decide), hO.ld (show sK < 32 by decide),
    hs.get (i := sDomLen) (v := BitVec.ofNat 64 D.dl) (by simp), hs.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := hb.k2
  have := hb.doml
  rcases hb.dl with e | e <;> omega_arith

theorem Md.keep {D : FD} {mi : BitVec 64} {t u : State} (h : Md D mi t) (hm : u.mem = t.mem) {rs : List Reg}
    (k : Keep rs t u) (h0 : .x0 ∉ rs) : Md D mi u :=
  (h.inn.keep hm k h0).md (h.r2f.mem hm)

/-- `x9` into the header slot `sF`. -/
theorem stF_g {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx) :
    WP isa (.block [sth .x9 sF]) t fun u => u.mem = t.mem.writeW (off G (8 * sF)) (t.gpr .x9) ∧ Keep [] t u := by
  have h8 := hdr_lt_slot w 8 (show sF < 32 by decide)
  exact WP.keep [] (Q := fun u => u.mem = t.mem.writeW (off G (8 * sF)) (t.gpr .x9))
    (by brun [hg.x0, hdr_enc (show sF < 32 by decide), hg.scr.st (show 8 * sF + 8 ≤ Zx by omega_arith)]) rfl rfl rfl

/-- `x9` into the inner header's `sF`, and back to the outer workspace. -/
theorem In.stLeave {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    WP isa (.block [sth .x9 sF, Crt.leave]) t fun u => (Pa D mi u ∧
      word u.mem (off D.B (inner D.w)) (8 * sF) = t.gpr .x9 ∧
      Outside (off D.B (inner D.w)) (8 * sF) 8 t.mem u.mem) ∧ KX t u := by
  have hg := h.2.1.good
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot D.w 8 (show sF < 32 by decide)
  rw [show [sth .x9 sF, Crt.leave] = [sth .x9 sF] ++ [Crt.leave] from rfl, WP.block_append_iff]
  refine WP.mono (stF_g hg (Nat.le_refl _)) fun u ⟨hm, k⟩ => ?_
  have o := writeW_outside t.mem (off D.B (inner D.w)) (d := 8 * sF) (t.gpr .x9) (by omega_arith)
  rw [← hm] at o
  have h₁ : In D mi u := h.step (rs := [(8 * sF, 8)]) (Frm.of_outside o (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := hdr_lt_slot D.w 0 (show sF < 32 by decide)
    have := slot_le (w := D.w) (show aN < 8 by decide)
    have := hdr_lt_slot D.w aN (show sF < 32 by decide)
    have := hdr_lt_slot D.w aOne (show sF < 32 by decide)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [sF, sFn] at * <;> omega_arith) k.rd k.wr (k.gpr .x0 (by decide))
  refine WP.mono (leave_ok h₁.2.1) fun v ⟨⟨h0, hm'⟩, k'⟩ => ⟨⟨h₁.pa hm' k' h0, ?_, ?_⟩,
    keep_trans (k.mono (by decide)) (k'.mono (by decide))⟩
  · rw [hm', hm]; exact word_writeW_self _ _ _ _
  · rw [hm']; exact o

end VG.Proof.Ffdh.AArch64
