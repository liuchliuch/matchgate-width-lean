import PaperStatements

/-! Proofs of the independently readable paper contracts. -/
namespace MatchgateWidth.Paper

theorem claim_3_1_verified : claim_3_1 :=
  @MatchgateWidth.source_integer_main_theorem_complete

theorem claim_3_2_verified : claim_3_2 :=
  @MatchgateWidth.no_universal_domain_bound_even_rational_graphs

theorem claim_3_3_verified : claim_3_3 :=
  @MatchgateWidth.allLeft_structural_trichotomy

theorem claim_3_3_family_verified : claim_3_3_family :=
  @MatchgateWidth.source_flag_alternative_unbounded

theorem claim_4_1_verified : claim_4_1 :=
  @MatchgateWidth.ExactMatchgate.reverse

theorem claim_4_2_verified : claim_4_2 :=
  @MatchgateWidth.field_preserving_matchgate_realization

theorem claim_4_3_transpose_verified : claim_4_3_transpose :=
  @MatchgateWidth.ExactMatchgateMatrix.transpose

theorem claim_4_3_pin_verified : claim_4_3_pin :=
  @MatchgateWidth.pin_lift_exact_coefficient_matrices

theorem claim_5_1_verified : claim_5_1 :=
  @MatchgateWidth.ExactMatchgate.trdeg_coordinateField_le

theorem claim_5_2_verified : claim_5_2 :=
  @MatchgateWidth.exact_sampled_star_coordinateField_bound

theorem claim_5_3_verified : claim_5_3 :=
  @MatchgateWidth.matchgateVariety_dimension_le

theorem claim_5_4_verified : claim_5_4 :=
  @MatchgateWidth.algebraic_star_table_bound

theorem claim_6_1_verified : claim_6_1 :=
  @MatchgateWidth.algebraicIndependent_primeExponentials_finite

theorem claim_6_2_verified : claim_6_2 :=
  @MatchgateWidth.transcendental_obstruction_proposition

theorem claim_6_3_verified : claim_6_3 :=
  @MatchgateWidth.lemma_6_3_positive_integer_grid_zariski_dense

theorem claim_6_4_verified : claim_6_4 :=
  @MatchgateWidth.exists_positive_integer_exact_obstruction

theorem claim_7_1_verified : claim_7_1 :=
  @MatchgateWidth.blockPfaffian_interpolation

theorem claim_8_1_verified : claim_8_1 :=
  @MatchgateWidth.controlled_rational_presentation_proposition

theorem claim_8_2_verified : claim_8_2 :=
  @MatchgateWidth.exists_controlled_ranks_and_support_proposition

theorem claim_8_3_verified : claim_8_3 :=
  @MatchgateWidth.twoCenter_coupling_proposition

theorem claim_8_4_verified : claim_8_4 :=
  @MatchgateWidth.transcendental_companion_presentation_proposition

theorem claim_9_1_verified : claim_9_1 :=
  @MatchgateWidth.transcendental_companion_arbitrary_instance_class

theorem claim_10_1_verified : claim_10_1 :=
  by
    intro S a b c n D inst I F p
    exact MatchgateWidth.AllLeftGadget.boundary_support_le I F p

theorem claim_10_2_verified : claim_10_2 :=
  @MatchgateWidth.qutrit_booleanBlock_support_of_rank_three

theorem claim_10_3_verified : claim_10_3 :=
  @MatchgateWidth.exact_rank_two_gaussian_hull

theorem claim_10_4_verified : claim_10_4 :=
  @MatchgateWidth.ExactMatchgateMatrix.exists_decoder

theorem claim_10_5_verified : claim_10_5 :=
  @MatchgateWidth.exact_labelwise_cover_compression

theorem claim_10_6_verified : claim_10_6 :=
  @MatchgateWidth.isotropic_kernel_cover_disk

theorem claim_10_7_verified : claim_10_7 :=
  @MatchgateWidth.source_connection_prime_collapse

theorem claim_10_8_verified : claim_10_8 :=
  @MatchgateWidth.exact_rank_two_block_decoding

theorem claim_10_9_lines_verified : claim_10_9_lines :=
  @MatchgateWidth.exact_all_line_supports_decomposition

theorem claim_10_9_flag_verified : claim_10_9_flag :=
  @MatchgateWidth.exact_uniform_flag_normal_form

theorem claim_10_10_verified : claim_10_10 :=
  @MatchgateWidth.allLeft_binary_context_corollary_any_generators

theorem claim_2_1_verified : claim_2_1 :=
  @MatchgateWidth.exactlyLabelledEquivalent_iff_on

theorem claim_2_2_existence_verified : claim_2_2_existence :=
  @MatchgateWidth.minimumExactCommonWidthOn_spec

theorem claim_2_2_minimum_verified : claim_2_2_minimum :=
  @MatchgateWidth.minimumExactCommonWidthOn_le

theorem claim_4_4_verified : claim_4_4 :=
  @MatchgateWidth.LabelledCommonPresentation.exactValidity

theorem claim_4_5_flag_verified : claim_4_5_flag :=
  @MatchgateWidth.allLeftMonomialFlag_iff

theorem claim_4_5_prime_verified : claim_4_5_prime :=
  @MatchgateWidth.allLeftConnectionPrime_iff

theorem claim_3_4_verified : claim_3_4 :=
  @MatchgateWidth.small_integer_flag_alternative

theorem claim_6_5_verified : claim_6_5 :=
  @MatchgateWidth.Effective.remark_6_5_effective_integer_obstruction

end MatchgateWidth.Paper
