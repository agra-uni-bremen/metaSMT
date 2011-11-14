add_tool_executable( sudoku 
  SOURCES 
    sudoku.cpp
  REQUIRES 
    Boolector_FOUND
    PicoSAT_FOUND
    MiniSat_FOUND
    Aiger_FOUND
    CUDD_FOUND
)

## run some sudokus as tests

if(sudoku_ENABLED)
set( _solvers boolector minisat picosat cudd graph_boolector graph_minisat graph_picosat graph_cudd)
set( _valid_instances
"n_gi_ldfbkc_eh_p_b_dmojnp_gfq_kilpf_ei_b_qn_m__jcm__g___j_e_f__b_kp___lcdb__jmhqm_b_f____ni__l_____fp_e___hcb_ngon_l_h_j__meif_k___po_f_n_l_g___fi_bh__p__d_oqjldg__kebqfc_jnimh_e_n__ilqob_dpc__qdc__piheo__gfmbf_____o_dklh___p_e_lbg_m_qn_ji_i___d_hec_jpkbq_"

"n_gi_ld_bkc_eh_p_b_dmojnp_gfq_kilp__ei_b_qn_m__jcm__g___j_e_f__b_kp___lcdb__jmhqm_b______ni__l_____fp_e___hcb_ngon_l_h_j__mei__k___po_f_n_l_g____i_bh__p__d_oqjldg__kebqfc_jnimh_e_n__ilqob_dpc__qdc__piheo__g_mbf_____o_dklh___p_e_lbg_m_qn_ji_i___d_hec_jpkbq_"

"____________eh_p_b_dmojnp_gfq_kilp__ei_b_q__m__jcm__g___j_e_f__b_kp____cdb__jmhqm_b______ni__l_____fp_e___hcb__gon___h_j____________________g____i_bh__p__d_oqj_dg__kebqfc_jnimh_e____il_________________eo__g_mbf_____o__________________qn_ji_i___d_hec_jpkbq_"

"_jebflm__d_o__i___i_dqk_b__ehfo__q_____cp__n__j_g_of_j__qlimd_ke___j_h_f__bgp__cmbf_ocj__e______qp_____bj__cf_nokc_ni_qmo_fpld__fen_h___l___gb___d____leckm_i__nh_m__d_k__e__j_q______p__ng___l_eijmbnclk_d__p____lkq__jn__h_e_ip____i__e________fchgk_oi__lj__d"

"___________o__i___i_dqk_b__ehfo__q_____cp__n____________qlimd_ke___j_h_f__bgp__cmbf_ocj__e______qp_____bj__cf_nokc_ni_qmo_fpld__fen_h___l___gb___d____leckm_i__nh_m__d_k__e__j_q______p__ng___l___________d__p____lkq__jn__h_e__________e________fchgk_oi__lj__d"

"__________________________________________________i_____bg_______________h___________________________________________b____________g__________________f____________kn_______________c____________________________________________________________________________"
)
set( _invalid_instances
"n_gi_ldfbkc_eh_p_b_dmojnp_gfq_kilpf_ei_b_qn_m__jcm__g___j_e_f__b_kp___lcdb__jmhqm_b_f____ni__l_____fp_e___hcb_ngon_l_h_j__meif_k___po_f_n_l_g___fi_bh__p__d_oqjldg__kebqac_jnimh_e_n__ilqob_dpc__qdc__piheo__gfmbf_____o_dklh___p_e_lbg_m_qn_ji_i___d_hec_jpkbq_"
)

set(sid 0)
foreach(s ${_solvers})
  set(iid 0)
  foreach(i ${_valid_instances})
    add_test(sudoku_${s}_valid_${iid} sudoku ${sid} ${i})
    math(EXPR iid "${iid} + 1")
  endforeach(i)
  set(iid 0)
  foreach(i ${_invalid_instances})
    set(_name sudoku_${s}_invalid_${iid})
    add_test(${_name} sudoku ${sid} ${i})
    set_property(TEST ${_name} PROPERTY WILL_FAIL TRUE)
    math(EXPR iid "${iid} + 1")
  endforeach(i)
  math(EXPR sid "${sid} + 1")
endforeach()

endif()
