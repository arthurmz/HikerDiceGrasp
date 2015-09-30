/*
 * hikerdice_branchandbound.h
 *
 *  Created on: 14 de set de 2015
 *      Author: Arthur
 */

#ifndef HIKERDICE_BRANCHANDBOUND_H_
#define HIKERDICE_BRANCHANDBOUND_H_

#include <stdio.h>
#include "graph.h"

void print_solution(float time_elapsed);
void init_data();
void config_pontuacao_max();
void init_graph(FILE *fp, int dice_i_pos, int dice_j_pos);
void add_childs(vertex* atual, vertex** stack);
void avaliar_melhor_solucao();
void roll_dice(vertex* actualVertex, vertex *vertexPai);
int fake_roll_dice(vertex* actualVertex, vertex *vertexPai);
int relacaoPaiFilho(vertex* filho, vertex* pai);



#endif /* HIKERDICE_BRANCHANDBOUND_H_ */
