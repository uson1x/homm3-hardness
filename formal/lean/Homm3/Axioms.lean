import Homm3.Theorem1
import Homm3.Prop11General
import Homm3.Health
import Homm3.Certificate
import Homm3.Theorem2
import Homm3.Theorem4
import Homm3.LemmaE20
import Homm3.BoardCheck
import Homm3.Gadgets
import Homm3.EmbedCheck
import Homm3.Step0
import Homm3.Step1

/-!
# Axiom audit

`lake build` prints the axioms each headline theorem depends on.  Expected: only
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no custom axioms).
-/

#print axioms Homm3.strike_radius
#print axioms Homm3.lemmaE1
#print axioms Homm3.lemmaE1_once
#print axioms Homm3.damage_neg_one_eq_iff
#print axioms Homm3.Knapsack.dp_eq_OPT
#print axioms Homm3.Corridor.dist_p_e_ne
#print axioms Homm3.Corridor.upper
#print axioms Homm3.Corridor.lower
#print axioms Homm3.Corridor.prop11_opt
#print axioms Homm3.Corridor.prop11_decide
#print axioms Homm3.Corridor.theorem1
#print axioms Homm3.Corridor.theorem1_total
#print axioms Homm3.mem_reach_univ_iff
#print axioms Homm3.lemmaE9
#print axioms Homm3.Corridor.pmr
#print axioms Homm3.prop11_general
#print axioms Homm3.prop11_general_decide
#print axioms Homm3.Corridor.prop11_decide_via_general
#print axioms Homm3.EHealth.equivPool
#print axioms Homm3.EHealth.kills_eq
#print axioms Homm3.Stack.kills_engine
#print axioms Homm3.Stack.hit_engine
#print axioms Homm3.step_iff_mem_succs
#print axioms Homm3.armyAllocation_iff
#print axioms Homm3.valueAO_attained
#print axioms Homm3.armyAllocation_iff_cert
#print axioms Homm3.Knapsack.dpArray_eq_dp
#print axioms Homm3.prop11_preprocess
#print axioms Homm3.prop11_general_decide_array
#print axioms Homm3.ThreeP.of_disjoint
#print axioms Homm3.ledger
#print axioms Homm3.Fam.fam_no
#print axioms Homm3.Thm2.sep
#print axioms Homm3.Thm2.sep_tight
#print axioms Homm3.Thm2.flower
#print axioms Homm3.Thm2.lemmaE12
#print axioms Homm3.Thm2.yes
#print axioms Homm3.Thm2.theorem2
#print axioms Homm3.theorem2_total
#print axioms Homm3.reach_row
#print axioms Homm3.ThmF.lemmaE16
#print axioms Homm3.ThmF.clear_of_AO
#print axioms Homm3.ThmF.route
#print axioms Homm3.ThmF.lemmaE18
#print axioms Homm3.ThmF.lemmaE19
#print axioms Homm3.ThmF.lemmaE21
#print axioms Homm3.ThmF.lemmaE22
#print axioms Homm3.ThmF.theorem4
#print axioms Homm3.theorem4_total
#print axioms Homm3.ThmF.cor41
#print axioms Homm3.cor41_total
#print axioms Homm3.ThmF.Fam.hp_no
#print axioms Homm3.ThmF.cor42
#print axioms Homm3.cor42_total
#print axioms Homm3.orderInv
#print axioms Homm3.wait_attack_defended
#print axioms Homm3.Fam.lemmaE2
#print axioms Homm3.Fam.ledgerW
#print axioms Homm3.ThmF.lemmaE20
#print axioms Homm3.ThmF.distinct_hexes
#print axioms Homm3.ThmF.seat_capacity
#print axioms Homm3.lemma32
#print axioms Homm3.blow_resource
#print axioms Homm3.X3C.card_cover
#print axioms Homm3.mem_reach_of_rtg
#print axioms Homm3.X3CBoard.reach_sub_region
#print axioms Homm3.X3CBoard.lemmaD1
#print axioms Homm3.ledgerB
#print axioms Homm3.T3.lemmaD5
#print axioms Homm3.T3.lemmaD6
#print axioms Homm3.T3.confinedLedger
#print axioms Homm3.T3.lemmaD7
#print axioms Homm3.T3.lemmaD9
#print axioms Homm3.T3.winning_unique
#print axioms Homm3.T3.witness
#print axioms Homm3.T3.lemmaD8
#print axioms Homm3.theorem3_core
#print axioms Homm3.theorem3
#print axioms Homm3.theorem3_pub
#print axioms Homm3.cor31_core
#print axioms Homm3.cor31
#print axioms Homm3.BoardData.check_sound
#print axioms Homm3.BoardData.D1_inv
#print axioms Homm3.theorem3_total
#print axioms Homm3.cor31_total
#print axioms Homm3.Gadgets.adj_shift
#print axioms Homm3.Gadgets.lemmaD2
#print axioms Homm3.Gadgets.enemy_gadget
#print axioms Homm3.Gadgets.lemmaD3
#print axioms Homm3.Gadgets.sep_constants
#print axioms Homm3.Gadgets.square_in_hex
#print axioms Homm3.Gadgets.old_draft_touch
#print axioms Homm3.BoardData.exactCover_iff_check
#print axioms Homm3.BoardData.yes_of
#print axioms Homm3.BoardData.no_of
#print axioms Homm3.Embed.lemmaD4
#print axioms Homm3.Embed.theorem3_drawing
#print axioms Homm3.Embed.theorem3_drawing'
#print axioms Homm3.Embed.cor31_drawing
#print axioms Homm3.Embed.build_size
#print axioms Homm3.Embed.OrthoDrawing.prox
#print axioms Homm3.Embed.OrthoDrawing.near_z
#print axioms Homm3.Embed.arms_side
#print axioms Homm3.Embed.sep_seg
#print axioms Homm3.Embed.DEdge.corr_iff
#print axioms Homm3.Embed.OrthoDrawing.check_sound
#print axioms Homm3.Embed.theorem3_drawing_total
#print axioms Homm3.Step0.step0_sound
#print axioms Homm3.Step0.cover_dedup
#print axioms Homm3.Step0.cover_zero
#print axioms Homm3.Step0.coverRaw_iff
#print axioms Homm3.Embed.Step1.card_V
#print axioms Homm3.Embed.Step1.card_E
