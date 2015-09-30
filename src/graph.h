/*
 * graph.h
 *
 *  Created on: 3 de set de 2015
 *      Author: Arthur
 */

#ifndef GRAPH_H_
#define GRAPH_H_

#include <stdbool.h>
#include "dice.h"

/**Atenção para NÃO focar na economia de memória.
 * Se um novo campo aumenta a velocidade de processamento do algoritmo,
 * este deve ser adicionado.
 */
typedef struct v{
	int i, j;
	bool visited;
	bool black;
	int tmp;//valor usado no guloso, para fazer o swap dos melhores movimentos na hora de add os filhos
	dice* d;//dado associado
} vertex;





#endif /* GRAPH_H_ */
