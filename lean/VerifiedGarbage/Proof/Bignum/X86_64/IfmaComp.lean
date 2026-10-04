import VerifiedGarbage.Proof.Bignum.X86_64.IfmaGlue
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaVecR

/-!
# RSA with AVX512_IFMA on x86-64: `ifma`

`ifma_ok`: the IFMA area after `q`'s workspace, both regions, the vector
code, and the results back in the primes' workspaces.

`IMem` gathers what holds throughout: `n`'s header, the primes' headers
(their workspace slots, `sMaskX` and `sIfma`), moduli and ones, and `n`'s
slots for the exponents; `IMem.of_frm` keeps it across any change within
`ifmaR`, the ranges `ifma` writes.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-- The ranges `ifma` writes, but its first two stores. -/
def ifmaR (op oq a : Nat) : List (Nat × Nat) :=
  shiftRanges op (k1Ranges 16 ++ resRanges) ++ shiftRanges oq (k1Ranges 16 ++ resRanges) ++ [(a, 2 * D + 8)]

/-- What `ifma` keeps, but the area's base in the primes' headers. -/
structure IPre (m : Mem) (B : Addr) (w op oq : Nat) (minv mp mq mk : BitVec 64) (P Q : Nat) (ep eq : Addr)
    (lp lq : Nat) : Prop where
  nh : Hdr m B w minv
  wsP : word m B (8 * sWsP) = off B op
  wsQ : word m B (8 * sWsQ) = off B oq
  pws : WsAt m B op 16 mp
  qws : WsAt m B oq 16 mq
  pn : wv m (off B op) (slot 16 Public.aN) 16 = P
  pinv : ((word m (off B op) (slot 16 Public.aN)).toNat * mp.toNat + 1) % 2 ^ 64 = 0
  pone : wv m (off B op) (slot 16 Public.aOne) 16 = 1
  qn : wv m (off B oq) (slot 16 Public.aN) 16 = Q
  qinv : ((word m (off B oq) (slot 16 Public.aN)).toNat * mq.toNat + 1) % 2 ^ 64 = 0
  qone : wv m (off B oq) (slot 16 Public.aOne) 16 = 1
  pmk : word m (off B op) (8 * sMaskX) = mk
  dp : word m B (8 * sDp) = ep
  pl : word m B (8 * sPlen) = BitVec.ofNat 64 lp
  dq : word m B (8 * sDq) = eq
  ql : word m B (8 * sQlen) = BitVec.ofNat 64 lq

/-- What `ifma` keeps. -/
structure IMem (m : Mem) (B : Addr) (w op oq a : Nat) (minv mp mq mk : BitVec 64) (P Q : Nat) (ep eq : Addr)
    (lp lq : Nat) : Prop extends IPre m B w op oq minv mp mq mk P Q ep eq lp lq where
  pia : word m (off B op) (8 * sIfma) = off B a
  qia : word m (off B oq) (8 * sIfma) = off B a

/-- What `IPre` reads: below `p`'s workspace, the first 29 slots of a
prime's header, and its modulus and one. -/
def IKept (op oq d n : Nat) : Prop :=
  d + n ≤ op ∨ (op ≤ d ∧ d + n ≤ op + 8 * 29) ∨ (d = op + slot 16 Public.aN ∧ n ≤ 128) ∨
    (d = op + slot 16 Public.aOne ∧ n ≤ 128) ∨ (oq ≤ d ∧ d + n ≤ oq + 8 * 29) ∨
    (d = oq + slot 16 Public.aN ∧ n ≤ 128) ∨ (d = oq + slot 16 Public.aOne ∧ n ≤ 128)

theorem ifmaR_disj {op oq a d n : Nat} (hpq : op + slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + slot 16 8 + tabBytes 16 ≤ a)
    (h : IKept op oq d n ∨ (d = op + 8 * sIfma ∧ n = 8) ∨ (d = oq + 8 * sIfma ∧ n = 8)) :
    ∀ r ∈ ifmaR op oq a, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have hT : tabBytes 16 = 2304 := rfl
  have hs : ∀ j, slot 16 j = 256 + j * 144 := fun j => by unfold slot hdrBytes; omega
  simp only [IKept, Public.aN, Public.aOne, hs, sIfma, sFn] at h
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, CrtIfma.sCtr, sFn, hs,
    Public.aAcc, Public.aTmp, Public.aY, aT] at hpq hqa ⊢
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

theorem ifmaR_le {op oq a : Nat} (hpq : op + slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + slot 16 8 + tabBytes 16 ≤ a) : ∀ r ∈ ifmaR op oq a, r.1 + r.2 ≤ a + 2 * D + 8 := by
  have hT : tabBytes 16 = 2304 := rfl
  have hs : ∀ j, slot 16 j = 256 + j * 144 := fun j => by unfold slot hdrBytes; omega
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, CrtIfma.sCtr, sFn, hs,
    Public.aAcc, Public.aTmp, Public.aY, aT] at hpq hqa ⊢
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

theorem IPre.of_frm {m m' : Mem} {B : Addr} {w op oq : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (h : IPre m B w op oq minv mp mq mk P Q ep eq lp lq) {rs : List (Nat × Nat)}
    (hf : Frm B rs m m') (hr : ∀ d n, IKept op oq d n → ∀ r ∈ rs, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hlo : slot w 8 ≤ op) (hpq : op + slot 16 8 + tabBytes 16 ≤ oq) (hz : oq + slot 16 8 ≤ 2 ^ 64) :
    IPre m' B w op oq minv mp mq mk P Q ep eq lp lq := by
  have hT : tabBytes 16 = 2304 := rfl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have := slot_le (w := 16) (show Public.aN < 8 by decide)
  have := slot_le (w := 16) (show Public.aOne < 8 by decide)
  have hW : ∀ d, IKept op oq d 8 → word m' B d = word m B d := fun d hk =>
    hf.word_eq (hr d 8 hk) (by unfold IKept at hk; omega)
  have hV : ∀ d, IKept op oq d 128 → wv m' B d 16 = wv m B d 16 := fun d hk =>
    hf.wv_eq (hr d 128 hk) (by unfold IKept at hk; omega)
  have hn : ∀ i < 32, word m' B (8 * i) = word m B (8 * i) := fun i hi => hW _ (.inl (by omega))
  have hp : ∀ i < 29, word m' (off B op) (8 * i) = word m (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inl ⟨by omega, by omega⟩))
  have hq : ∀ i < 29, word m' (off B oq) (8 * i) = word m (off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))
  refine ⟨⟨(hn _ (by decide)).trans h.nh.hw, (hn _ (by decide)).trans h.nh.hminv,
      fun j hj => (hn _ (by unfold sArr; omega)).trans (h.nh.harr j hj)⟩,
    (hn _ (by decide)).trans h.wsP, (hn _ (by decide)).trans h.wsQ,
    h.pws.of_words fun i hi => hp i (by omega), h.qws.of_words fun i hi => hq i (by omega),
    ?_, ?_, ?_, ?_, ?_, ?_, (hp _ (by decide)).trans h.pmk, (hn _ (by decide)).trans h.dp,
    (hn _ (by decide)).trans h.pl, (hn _ (by decide)).trans h.dq, (hn _ (by decide)).trans h.ql⟩
  · rw [wv_off, hV _ (.inr (.inr (.inl ⟨rfl, le_refl _⟩))), ← wv_off]; exact h.pn
  · rw [word_off, hW _ (.inr (.inr (.inl ⟨rfl, by decide⟩))), ← word_off]; exact h.pinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inl ⟨rfl, le_refl _⟩)))), ← wv_off]; exact h.pone
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, le_refl _⟩)))))), ← wv_off]; exact h.qn
  · rw [word_off, hW _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, by decide⟩)))))), ← word_off]; exact h.qinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, le_refl _⟩)))))), ← wv_off]; exact h.qone

theorem IMem.of_frm {m m' : Mem} {B : Addr} {w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (h : IMem m B w op oq a minv mp mq mk P Q ep eq lp lq)
    (hf : Frm B (ifmaR op oq a) m m') (hlo : slot w 8 ≤ op) (hpq : op + slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + slot 16 8 + tabBytes 16 ≤ a) (hz : a ≤ 2 ^ 64) :
    IMem m' B w op oq a minv mp mq mk P Q ep eq lp lq := by
  have hT : tabBytes 16 = 2304 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  refine ⟨h.toIPre.of_frm hf (fun d n hk => ifmaR_disj hpq hqa (.inl hk)) hlo hpq (by omega), ?_, ?_⟩
  · rw [word_off, hf.word_eq (ifmaR_disj hpq hqa (.inr (.inl ⟨rfl, rfl⟩))) (by unfold sIfma sFn; omega), ← word_off]
    exact h.pia
  · rw [word_off, hf.word_eq (ifmaR_disj hpq hqa (.inr (.inr ⟨rfl, rfl⟩))) (by unfold sIfma sFn; omega), ← word_off]
    exact h.qia

/-! ## `ifma`'s first half: the regions -/

/-- `ifma`'s first block, from `n`'s workspace to `p`'s. -/
theorem headI_ok {s : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : IPre s.mem B w op oq minv mp mq mk P Q ep eq lp lq) (hlo : slot w 8 ≤ op)
    (hpq : op + slot 16 8 + tabBytes 16 ≤ oq) (ha : a = oq + slot 16 8 + tabBytes 16) (haZ : a + 2 * D + 8 ≤ Z) :
    WP isa (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))) s fun u =>
      IMem u.mem B w op oq a minv mp mq mk P Q ep eq lp lq ∧
      Frm B [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] s.mem u.mem ∧ u.gpr .rdi = off B op ∧
      Keep [.rax, .rdx, .rdi] s u := by
  have hn := hs.nowrap
  have hT : tabBytes 16 = 2304 := rfl
  have hD : D = 3712 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  subst ha
  refine WP.mono (ifmaHead_ok ⟨hs, hdi, h.nh⟩ hlo hpq (by omega) h.wsP h.wsQ h.qws) fun u ⟨me, di, k⟩ => ?_
  have o1 := writeW_outside s.mem B (d := op + 8 * sIfma) (off (off B oq) (slot 16 8 + tabBytes 16))
    (by unfold sIfma sFn; omega)
  have o2 := writeW_outside (s.mem.writeW (off B (op + 8 * sIfma)) (off (off B oq) (slot 16 8 + tabBytes 16))) B
    (d := oq + 8 * sIfma) (off (off B oq) (slot 16 8 + tabBytes 16)) (by unfold sIfma sFn; omega)
  rw [off_off B op, off_off B oq (8 * sIfma)] at me
  have f : Frm B [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] s.mem u.mem := by
    rw [me]
    exact (Frm.of_outside o1 (List.mem_cons_self ..)).trans
      (Frm.of_outside o2 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hia : off (off B oq) (slot 16 8 + tabBytes 16) = off B (oq + slot 16 8 + tabBytes 16) := by
    rw [off_off, Nat.add_assoc]
  refine ⟨⟨h.of_frm f (fun d n hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hs : ∀ j, slot 16 j = 256 + j * 144 := fun j => by unfold slot hdrBytes; omega
      simp only [IKept, hs, Public.aN, Public.aOne] at hk
      rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega) hlo hpq
      (by omega), ?_, ?_⟩, f, di, k⟩
  · rw [word_off, me, o2.word (.inl (by unfold sIfma sFn; omega)) (by unfold sIfma sFn; omega), ← hia]
    exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · rw [word_off, me, ← hia]
    exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _

/-- From one workspace (`rdi = off B o`, linked to `B`) to the one in `n`'s slot `sl`. -/
theorem swapWs_ok {u : State} {B : Addr} {Z o o' sl : Nat} (hs : Scr u B Z) (hdi : u.gpr .rdi = off B o)
    (hlk : word u.mem (off B o) (8 * sLink) = B) (hsl : word u.mem B (8 * sl) = off B o') (hsl' : sl < 32)
    (ho : o + 8 * 32 ≤ Z) :
    WP isa (.block [leave, .mov .rdi (.mem (hdr sl))]) u fun u' =>
      u'.gpr .rdi = off B o' ∧ u'.mem = u.mem ∧ Keep [.rdi] u u' := by
  have hl : InRegions (u.rd ++ u.wr) (off (off B o) (8 * sLink)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  have hl' : InRegions (u.rd ++ u.wr) (off B (8 * sl)) 8 := hs.ld (by omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun u' => u'.gpr .rdi = off B o' ∧ u'.mem = u.mem) (by
    xrun [leave, State.ea, hdr, hdi, hdrOff, hl, hlk, hl', hsl]) rfl) fun u' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

theorem k1sh_lt (o : Nat) : ∀ r ∈ shiftRanges o (k1Ranges 16), o + 8 * 30 ≤ r.1 ∧ r.1 + r.2 ≤ o + slot 16 8 := by
  have hs : ∀ j, slot 16 j = 256 + j * 144 := fun j => by unfold slot hdrBytes; omega
  simp only [shiftRanges, k1Ranges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    CrtIfma.sCtr, sFn, hs, Public.aAcc, Public.aTmp, aT]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem k1sh_ifmaR (op oq a : Nat) {o : Nat} (ho : o = op ∨ o = oq) :
    ∀ r ∈ shiftRanges o (k1Ranges 16), r ∈ ifmaR op oq a := fun r hr => by
  simp only [ifmaR, shiftRanges, List.map_append, List.mem_append] at hr ⊢
  rcases ho with rfl | rfl
  · exact .inl (.inl (.inl hr))
  · exact .inl (.inr (.inl hr))

theorem regFr_ifmaR {op oq a o p : Nat} (ho : o = op ∨ o = oq) (hp : p < 2) :
    ∀ r ∈ shiftRanges o (k1Ranges 16) ++ [(a + D * p, D)], ∃ r' ∈ ifmaR op oq a,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun r hr => by
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, k1sh_ifmaR op oq a ho r hr, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(a, 2 * D + 8), List.mem_append_right _ (List.mem_singleton_self _),
      by rw [List.mem_singleton.mp hr]; simp only; omega⟩

/-- `ifma`'s first half: the area's base, and both regions. -/
theorem ifmaA_ok {s : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {ebp ebq : List Byte} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : IPre s.mem B w op oq minv mp mq mk P Q ep eq ebp.length ebq.length) (hlo : slot w 8 ≤ op)
    (hpq : op + slot 16 8 + tabBytes 16 ≤ oq) (ha : a = oq + slot 16 8 + tabBytes 16) (haZ : a + 2 * D + 8 ≤ Z)
    (hYp : wv s.mem (off B op) (slot 16 Public.aY) 16 < P) (hYq : wv s.mem (off B oq) (slot 16 Public.aY) 16 < Q)
    (hep : Src s B Z ep ebp) (heq : Src s B Z eq ebq) (hLp1 : 1 ≤ ebp.length) (hLp2 : ebp.length ≤ 128)
    (hLq1 : 1 ≤ ebq.length) (hLq2 : ebq.length ≤ 128) :
    WP isa (seqs (([.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))] : List (Prog isa)) ++ (CrtIfma.region 0 sDp sPlen ++
      (([.block [leave, enterQ]] : List (Prog isa)) ++ CrtIfma.region 1 sDq sQlen)))) s fun t =>
      IMem t.mem B w op oq a minv mp mq mk P Q ep eq ebp.length ebq.length ∧
      RegOut t.mem (off B a) 0 P (2 ^ 32 * wv s.mem (off B op) (slot 16 Public.aY) 16 % P)
        (wv s.mem (off B op) (slot 16 aXc) 16) (wv s.mem (off B op) (slot 16 Public.aY) 16)
        (wv s.mem (off B op) (slot 16 Public.aY) 16) (mp &&& mask52) ebp ∧
      RegOut t.mem (off B a) 1 Q (2 ^ 32 * wv s.mem (off B oq) (slot 16 Public.aY) 16 % Q)
        (wv s.mem (off B oq) (slot 16 aXc) 16) (wv s.mem (off B oq) (slot 16 Public.aY) 16) 1
        (mq &&& mask52) ebq ∧
      Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR op oq a) s.mem t.mem ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ t.gpr .rdi = off B oq ∧ Keep (mmRegs ++ ([.rdi] : List Reg)) s t := by
  have hn := hs.nowrap
  have hT : tabBytes 16 = 2304 := rfl
  have hD : D = 3712 := rfl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have lY := slot_le (w := 16) (show Public.aY < 8 by decide)
  have lC := slot_le (w := 16) (show aXc < 8 by decide)
  have hY0 := hdr_lt_slot 16 Public.aY (show 31 < 32 by decide)
  have hC0 := hdr_lt_slot 16 aXc (show 31 < 32 by decide)
  -- The head.
  refine wp_seqs_append (by simp) (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (WP.mono
    (headI_ok hs hdi h hlo hpq ha haZ) fun u₁ ⟨m₁, f₁, d₁, k₁⟩ => ?_)
  have hf₁ : ∀ {d n}, d + n ≤ op + 8 * sIfma ∨ (op + 8 * sIfma + 8 ≤ d ∧ d + n ≤ oq + 8 * sIfma) ∨
      oq + 8 * sIfma + 8 ≤ d → ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], d + n ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
  have hYp₁ : wv u₁.mem (off B op) (slot 16 Public.aY) 16 = wv s.mem (off B op) (slot 16 Public.aY) 16 := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hCp₁ : wv u₁.mem (off B op) (slot 16 aXc) 16 = wv s.mem (off B op) (slot 16 aXc) 16 := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hZ₁ : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], r.1 + r.2 ≤ Z := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega
  -- `p`'s region.
  refine wp_seqs_append (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (by simp) (WP.mono
    (region_ok (p := 0) (SubCtx.mk' (hs.congr k₁.2.2) m₁.nh m₁.pws d₁ hlo (by omega)) m₁.pia (by omega) haZ
      (by decide) m₁.pn (by rw [hYp₁]; exact hYp) (by decide) (by decide) m₁.dp m₁.pl
      (hep.congr (InScr.of_frm f₁ hZ₁) k₁.2.1 k₁.2.2) hLp1 hLp2) fun u₂ ⟨rp, f₂, w₂, d₂, k₂⟩ => ?_)
  have f₂' := f₂.widen (regFr_ifmaR (oq := oq) (.inl rfl) (by decide))
  have m₂ := m₁.of_frm f₂' hlo hpq (by omega) (by omega)
  have F₂ : Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR op oq a) s.mem u₂.mem :=
    (f₁.mono fun r hr => List.mem_append_left _ hr).trans (f₂'.mono fun r hr => List.mem_append_right _ hr)
  have hZF : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR op oq a, r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hZ₁ r hr
    · have := ifmaR_le hpq (by omega) r hr; omega
  -- To `q`'s workspace.
  refine wp_seqs_append (by simp) (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (WP.mono
    (swapWs_ok (o' := oq) (hs.congr (w₂.trans k₁.2.2)) d₂ m₂.pws.link m₂.wsQ (by decide) (by omega))
    fun u₃ ⟨d₃, me₃, k₃⟩ => ?_)
  rw [← me₃] at m₂ F₂
  have hq₃ : ∀ j, j < 8 → j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ aT →
      wv u₃.mem (off B oq) (slot 16 j) 16 = wv s.mem (off B oq) (slot 16 j) 16 := fun j hj h1 h2 h3 => by
    have := slot_le (w := 16) hj
    have := hdr_lt_slot 16 j (show 31 < 32 by decide)
    rw [wv_off, wv_off, me₃, f₂.wv_eq (fun r hr => ?_) (by omega),
      f₁.wv_eq (hf₁ (.inr (.inr (by unfold sIfma sFn; omega)))) (by omega)]
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := k1sh_lt op r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)
  have k₁₃ := (k₁.trans k₂).trans k₃
  -- `q`'s region.
  refine WP.mono (region_ok (p := 1) (SubCtx.mk' (hs.congr k₁₃.2.2) m₂.nh m₂.qws d₃ (by omega) (by omega)) m₂.qia
    (by omega) haZ (by decide) m₂.qn (by rw [hq₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hYq)
    (by decide) (by decide) m₂.dq m₂.ql (heq.congr (InScr.of_frm F₂ hZF) k₁₃.2.1 k₁₃.2.2) hLq1 hLq2)
    fun t ⟨rq, f₄, w₄, d₄, k₄⟩ => ?_
  have f₄' := f₄.widen (regFr_ifmaR (op := op) (.inr rfl) (by decide))
  rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (0 : Nat) = 0)), hYp₁, hCp₁, ← me₃] at rp
  simp only [Nat.one_ne_zero, ↓reduceIte] at rq
  rw [hq₃ _ (by decide) (by decide) (by decide) (by decide),
    hq₃ _ (by decide) (by decide) (by decide) (by decide)] at rq
  refine ⟨m₂.of_frm f₄' hlo hpq (by omega) (by omega), rp.of_frm f₄ (fun r hr => ?_) (by omega), rq,
    F₂.trans (f₄'.mono fun r hr => List.mem_append_right _ hr), w₄.trans k₁₃.2.2, ?_, d₄,
    k₁₃.trans k₄ |>.mono (by simp [mmRegs])⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := k1sh_lt oq r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)
  · rw [k₄.2.1, k₁₃.2.1]

end VG.Proof.Bignum.X86_64
