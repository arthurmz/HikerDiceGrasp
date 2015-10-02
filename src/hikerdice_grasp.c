/*
 ============================================================================
 Name        : hikerdice_guloso.c
 Author      : Arthur
 Version     : 1
 Copyright   : WTFPL
 Description : Algoritmo guloso para a solução do problema do Hiker Dice Hamiltoniano

 ============================================================================
 */

#include "hikerdice_grasp.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include <float.h>
#include <time.h>
#include "dice.h"
#include "graph.h"

/** ================================================= Data =================================*/
vertex** matrix;//uma matriz

int m_, n_;//altura e largura do grafo
int total_free_vertexes;//total de vertices livres (nao pretos)

vertex** stack;//pilha de busca do branch and bound
int head_stack;//cabeca da pilha de busca

vertex* origin;//vertice de saida
vertex** melhor_solucao;//sequencia de vertices da melhor solucao (array de ponteiros)

vertex** solucao_parcial;//sequencia de vertices da melhor solucao (array de ponteiros)
int head_solucao_parcial;//cabeca da solucao parcial

int pontuacao_melhor_solucao;//Pontuacao da melhor solucao
int pontuacao_parcial;//pontuacao parcial sendo construida
int vertex_restantes;

int *pontuacao_max_para_cada_numero_jogadas;

//=============== parte do GRASP
vertex*** solucoes_iniciais;//vetor para um vertex** (que por sua vez é um vetor de vertex*)
int populacao_solucao_inicial;//tamanho da população inicial
//================fim da parte do GRASP

unsigned long long count_branches;
unsigned long long qtd_solucoes_validas;
unsigned long long qtd_bound_pontuacao_max;//qtd de retornos por pontuação máxima não pode melhorar
unsigned long long qtd_bound_null_black_visited;//qtd de retornos por vértice nulo ou prto ou visitado
unsigned long long qtd_bound_grau_vizinho_1;//qtd de retornos por grau de algum vizinho == 1


//parte da busca em profundidade p/ verificar a conexÃ£o do grafo
int vertex_atingidos;
vertex **vertex_visitados_profundidade;

/** ================================================= End Data =================================*/

/*Resolve o mapa usando o grasp
 *
 *
 * O algoritmo irá verificar e escolher a melhor dentre as seguintes 9 soluções
 *
 * solução gulosa baseada no vizinho com maior recompensa ('custo' da aresta)
 * solução seguindo as seguintes sequências de vizinhos de um vértice, da árvore de busca
 * esq - cima - direita - baixo
 * esq - baixo - direita - cima
 * cima - direita - baixo - esq
 * cima - esq - baixo - direita
 * direita - baixo - esq - cima
 * direita - cima - esq - baixo
 * baixo - esq - cima - direita
 * baixo - direita - cima - esquerda
 *
 *
 * Uma possível variação é a inserção de movimentos aleatórios
 * parâmetros:
 * % taxa de aleatorização (se vai escolher o próximo passo guloso ou aleatório)
 *
 *
 * Assim, as soluções não compartilham uma vizinhança explicia a nivel de estrutura de dados
 * mas compartilhan a FORMA de construção da solução.
 *
 *
 *
 * */

/*
 * 1ºpasso: Gerar N soluções guloso-aleatórias para posteriormente aplicar a busca local.
 * 			nessas N soluções iniciais, as 17 primeiras serão:
 * 			solução gulosa simples (sem aleatoriedade)
 * 			 solução seguindo as seguintes ordens de preferência de vizinhos de um vértice, na árvore de busca
 * 			 esq - cima - direita - baixo
 * 			 esq - baixo - direita - cima
 * 			 cima - direita - baixo - esq
 * 			 cima - esq - baixo - direita
 * 			 direita - baixo - esq - cima
 * 			 direita - cima - esq - baixo
 * 			 baixo - esq - cima - direita
 * 			 baixo - direita - cima - esquerda
 * 			 esq - dir - cima - baixo
 * 			 esq - dir - baixo - cima
 * 			 dir - esq - cima -baixo
 * 			 dir - esq - baixo -cima
 * 			 cima - baixo - esq - dir
 * 			 cima - baixo - dir - esq
 * 			 baixo - cima -esq- dir
 * 			 baixo - cima - dir -esq
 */
void solve(){
	generate_greedy_solutions();

}

//Gera N soluções semi-gulosas aleatórias
//a cada vértice vizitado, os seus vizinhos livres são hankeados de acordo com a pontuação que se obtem
//é feita uma roleta para decidir a ordem em que eles aparecerão para ser add na pilha
void generate_greedy_solutions(){
	for (int solution = 0; solution < populacao_solucao_inicial; solution++){
		reset_stack();
		add_childs(origin, stack);
		solucao_parcial[-1] = origin;
		bool has_found_solution = false;

		while (head_stack >= 0 && !has_found_solution){
			vertex* actual = stack[head_stack];
			if (!actual->visited){
				actual->visited = true;
				vertex_restantes--;
				solucao_parcial[head_solucao_parcial++] = actual;
				roll_dice(actual, solucao_parcial[head_solucao_parcial-2]);
				add_childs(actual, stack);
			}
			else{
				if (head_solucao_parcial == total_free_vertexes && pontuacao_melhor_solucao < pontuacao_parcial){
					for (int i = 0; i < total_free_vertexes; i++){
						melhor_solucao[i] = solucao_parcial[i];
					}
					pontuacao_melhor_solucao = pontuacao_parcial;
					qtd_solucoes_validas++;
					has_found_solution = true;
					continue;
				}

				//avaliar_melhor_solucao();
				actual->visited = false;
				pontuacao_parcial -= actual->d->bottom;
				head_stack--;
				head_solucao_parcial--;
				vertex_restantes++;
			}
		}
	}
}

/**Conta a quantidade de vizinhos livres de vtx, excluindo o atual*/
int count_vizinhos_livres(vertex *vtx, vertex* atual){
	int i = (*vtx).i;
	int j = (*vtx).j;
	int count = 0;
	if (j>0 && (&matrix[i][j-1] == origin
			|| (!matrix[i][j-1].visited && !matrix[i][j-1].black && &matrix[i][j-1] != atual) ))
		count++;
	if (i>0 && (&matrix[i-1][j] == origin
			|| (!matrix[i-1][j].visited && !matrix[i-1][j].black && &matrix[i-1][j] != atual) ))
		count++;
	if (j<n_-1 && (&matrix[i][j+1] == origin
			|| (!matrix[i][j+1].visited && !matrix[i][j+1].black && &matrix[i][j+1] != atual) ))
		count++;
	if (i<m_-1 && (&matrix[i+1][j] == origin
			|| (!matrix[i+1][j].visited && !matrix[i+1][j].black && &matrix[i+1][j] != atual) ))
		count++;
	return count;
}

/* Verifica se apos a insercao do next, os vizinhos do vertice atual continuam com grau 2,
 * excluindo o vertice vizinho que tambem eh vizinho do destino.
 */
bool vizinhos_atual_tem_grau_2_apos_insercao_next(vertex *atual, vertex *next, vertex *esq, vertex *cima, vertex *dir, vertex *baixo){
	if (atual == origin)
		return true;

	if (esq != NULL && !esq->black && !esq->visited
			&& esq != next && esq != origin && count_vizinhos_livres(esq, atual) < 2)
		return false;
	if (cima != NULL && !cima->black && !cima->visited
			&& cima != next && cima != origin && count_vizinhos_livres(cima, atual) < 2)
		return false;
	if (dir != NULL && !dir->black && !dir->visited
			&& dir != next && dir != origin && count_vizinhos_livres(dir, atual) < 2)
		return false;
	if (baixo != NULL && !baixo->black && !baixo->visited
			&& baixo != next && baixo != origin && count_vizinhos_livres(baixo, atual) < 2)
		return false;
	return true;
}

bool pontuacao_atual_pode_melhorar(){
	int pontuacao_max = pontuacao_max_para_cada_numero_jogadas[vertex_restantes];
	return ((pontuacao_max + pontuacao_parcial) > pontuacao_melhor_solucao);
}



void busca_profundidade(vertex *vtx){
	int i = (*vtx).i;
	int j = (*vtx).j;
	vtx->visited = true;
	vertex_visitados_profundidade[vertex_atingidos++] = vtx;

	vertex * next = NULL;
	if (j > 0) next = &matrix[i][j-1]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
	if (i>0) next = &matrix[i-1][j]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
	if (j < n_-1) next = &matrix[i][j+1]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
	if (i < m_-1) next = &matrix[i+1][j]; else next = NULL;
	if (next != NULL && !next->visited && !next->black){
		busca_profundidade(next);
	}
}

/**
 * Verifica se o grafo está conectado. fazendo uma busca em profundidade, e contando a quantidade de
 * vértices alcançados.
 */
bool grafo_conectado(vertex *next, vertex* atual){
	int vizinhos_livres = count_vizinhos_livres(next, atual);
	if (vizinhos_livres == 1) return true;
	//else if () Verificar o caso em que tem grau 2 ou 3
	vertex_atingidos = 0;

	busca_profundidade(next);

	//Desmarcando os visitados
	for (int i = 0; i < vertex_atingidos; i++){
		vertex_visitados_profundidade[i]->visited = false;
	}

	return (vertex_atingidos == total_free_vertexes - head_solucao_parcial);

}

/* Verifica as condicoees de insercao do next*/
bool insert_conditions(vertex *atual, vertex *next, vertex *esq, vertex *cima, vertex *dir, vertex *baixo){
	if (next == NULL || next->black || next->visited || (next == origin && vertex_restantes > 1)){
		qtd_bound_null_black_visited++;
		return false;
	}
	if (!pontuacao_atual_pode_melhorar()){
		qtd_bound_pontuacao_max++;
		return false;
	}
	if (!vizinhos_atual_tem_grau_2_apos_insercao_next(atual, next, esq, cima, dir, baixo)){
		qtd_bound_grau_vizinho_1++;
		return false;
	}
	//if (!grafo_conectado(next, atual)){
	//	return false;
	//}


	return true;
}

/*Adiciona os filhos na seguinte ordem:
 *Esq, Cima, Dir, e baixo
 *Assim, a busca ocorre do sentido anti-horï¿½rio: baixo, dir, cima e esq.
 */

/*Adiciona os filhos de 'atual', aplicando uma ordem gulosa que tenta escolher os mais bem aptos em cada sorteio.
 * No fim, essa ordem é revertida, já que o ultimo adicionado será o primeiro da cabeça da pilha
 */
void add_childs(vertex* atual, vertex** stack){
	int i = (*atual).i;
	int j = (*atual).j;
	vertex *vizinhoEsq = NULL;
	vertex *vizinhoCima = NULL;
	vertex *vizinhoDir = NULL;
	vertex *vizinhoBaixo = NULL;
	if (j>0) vizinhoEsq = &matrix[i][j-1];
	if (i>0) vizinhoCima = &matrix[i-1][j];
	if (j<n_-1) vizinhoDir = &matrix[i][j+1];
	if (i<m_-1) vizinhoBaixo = &matrix[i+1][j];

	int first_new_vtx = head_stack+1;//guarda a posição do primeiro novo elemento inserid

	if (insert_conditions(atual, vizinhoEsq, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoEsq;
		count_branches++;
	}
	if (insert_conditions(atual, vizinhoCima, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoCima;
		count_branches++;
	}
	if (insert_conditions(atual, vizinhoDir, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoDir;
		count_branches++;
	}
	if (insert_conditions(atual, vizinhoBaixo, vizinhoEsq, vizinhoCima, vizinhoDir, vizinhoBaixo)){
		stack[++head_stack] = vizinhoBaixo;
		count_branches++;
	}

	//================================ Mecanismo de ordenação guloso-aleatório========================
	int qtd_inseridos = head_stack - (first_new_vtx-1);
	if (first_new_vtx > 0 && qtd_inseridos > 1){
		float menor_valor_ponto = FLT_MAX;
		float pontuacao[4] = {0};//pontuação do vtx i, de acordo com a ordem de leitura.
		bool selecionados[4] = {0};
		float acc_pontuacao = 0;//acumulador da pontuacao
		vertex* subLista[4] = {0};
		int count_selecionados = 0;

		for (int i = first_new_vtx; i <= head_stack; i++){
			pontuacao[i-first_new_vtx] = fake_roll_dice(stack[i], stack[first_new_vtx-1]);
			if (pontuacao[i-first_new_vtx] < menor_valor_ponto)
				menor_valor_ponto = pontuacao[i-first_new_vtx];//pegando o menor valor
			acc_pontuacao += pontuacao[i-first_new_vtx];//pegando o acumulador
		}
		float diferenca = menor_valor_ponto - 1;//depois de calcular a diferença, dá pra subtrair as pontuações
		acc_pontuacao -= diferenca*qtd_inseridos;
		for (int i = first_new_vtx; i <= head_stack; i++){
			pontuacao[i-first_new_vtx] -= diferenca;//subtrai todos os pontos pra aproximar de 0 e maximizar as diferenças
			pontuacao[i-first_new_vtx] = pontuacao[i-first_new_vtx] / acc_pontuacao;//agora temos a % de cada vtx
		}
		while (count_selecionados < qtd_inseridos){
			float sorteado = ((double)rand()/(double)RAND_MAX);
			float acc_porcentagem = 0;//acumula as porcentagens para dar o 'pedaço da roleta'
			for (int i = first_new_vtx; i <= head_stack && count_selecionados < qtd_inseridos; i++){
				acc_porcentagem += pontuacao[i-first_new_vtx];
				if (sorteado < acc_porcentagem && !selecionados[i-first_new_vtx]){
					subLista[count_selecionados] = stack[i];
					selecionados[i-first_new_vtx] = 1;
					count_selecionados++;
				}
			}
		}

		//no fim, copia em ordem reversa pra pilha
		for (int i = first_new_vtx; i <= head_stack; i++){
			stack[i] = subLista[head_stack-i];
		}
	}
}




//Rolando o dado para o actualVertex
void roll_dice(vertex* actualVertex, vertex* vertexPai){
	if (vertexPai != NULL){
		dice *dadoAtual = (*actualVertex).d;
		dice *dadoPai = (*vertexPai).d;
		if (relacaoPaiFilho(actualVertex, vertexPai) == 1){
			pontuacao_parcial += roll_left(dadoAtual,dadoPai);//rolando o dado que ja esta no proximo vertice
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 2){
			pontuacao_parcial += roll_up(dadoAtual, dadoPai);//rolando o dado que ja esta no proximo vertice
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 3){
			pontuacao_parcial += roll_right(dadoAtual, dadoPai);//rolando o dado que ja esta no proximo vertice
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 4){
			pontuacao_parcial += roll_down(dadoAtual, dadoPai);//rolando o dado que ja esta no proximo vertice
		}
	}
}

//Rolando o dado para o actualVertex
int fake_roll_dice(vertex* actualVertex, vertex* vertexPai){
	if (vertexPai != NULL){
		int pontuacao = 0;
		dice *dadoAtual = (*actualVertex).d;
		dice *dadoPai = (*vertexPai).d;
		if (relacaoPaiFilho(actualVertex, vertexPai) == 1){
			pontuacao = fake_roll_left(dadoAtual, dadoPai);
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 2){
			pontuacao = fake_roll_up(dadoAtual, dadoPai);
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 3){
			pontuacao = roll_right(dadoAtual, dadoPai);
		}
		else if (relacaoPaiFilho(actualVertex, vertexPai) == 4){
			pontuacao = roll_down(dadoAtual, dadoPai);
		}
		return pontuacao;
	}
	return 0;
}


// 1 - esq, 2 - cima, 3 - direita, 4 - baixo
int relacaoPaiFilho(vertex* filho, vertex* pai){
	if((*filho).i == (*pai).i && (*filho).j == (*pai).j-1)
		return 1;
	if((*filho).i == (*pai).i-1 && (*filho).j == (*pai).j)
		return 2;
	if((*filho).i == (*pai).i && (*filho).j == (*pai).j+1)
		return 3;
	if((*filho).i == (*pai).i+1 && (*filho).j == (*pai).j)
		return 4;
	return 0;
}



int main(int argc, char *argv[]) {

	if (argc >= 2){
		FILE *file = fopen( argv[1], "r" );
		if ( file == 0 ){
			printf( "Impossivel abrir arquivo, encerrando\n" );
			return EXIT_SUCCESS;
		}else if (argc >= 5){
			printf("Arquivo encontrado: ");
			printf("%s",argv[1]);
			printf("\n");
			int dice_i_pos = argv[2][0] - 48;
			int dice_j_pos = argv[3][0] - 48;
			populacao_solucao_inicial = atoi(argv[4]);
			//populacao_solucao_inicial = argv[4][0] - 48;

			init_graph(file, dice_i_pos, dice_j_pos);
		}
		else {
			printf("Argumentos Insuficientes, insira: nome do arquivo, posição xy do dado e o tamanho da pop inicial");
			return EXIT_SUCCESS;
		}
		srand( (unsigned)time(NULL) );//preparando pra usar numeros aleatorios
		init_data();
		config_pontuacao_max();
		if (total_free_vertexes % 2 != 0){
			printf("O numero de casas livres eh impar. Nao existe solucao para o problema.");
			return EXIT_SUCCESS;
		}
		clock_t t;
		t = clock();
		solve();
		t = clock() - t;
		print_solution(((float)t)/CLOCKS_PER_SEC);
	}
	else {
		printf("Argumentos insuficientes\n" );
	}
	return EXIT_SUCCESS;
}


/**===================================== Funcoes de suporte ==============================================*/
void print_solution(float time_elapsed){
	printf("Solucao encontrada: ");
	if (pontuacao_melhor_solucao > 0){
		int k = 0;
		for (k = 0; k < total_free_vertexes && k < 1000; k++){
			printf("[%d,%d] ", melhor_solucao[k]->i, melhor_solucao[k]->j);
		}
		if (k < total_free_vertexes)
			printf("Solucao muito grande, impressao interrompida.");
	}
	printf("\nValor da melhor pontuacao: %d", pontuacao_melhor_solucao);
	printf("\nNumero de branches: %llu", count_branches);
	if (time_elapsed > 0)
		printf("\nTempo de processamento: %.3f segundos\n", time_elapsed);
	else {
		printf("\nTempo de processamento: 0.000 segundos\n");
	}
	printf("\nQuantidade de solucoes encontradas: %llu\n", qtd_solucoes_validas);
	printf("\nQtd de retornos por melhor pontuação alcançada: %llu\n", qtd_bound_pontuacao_max);
	printf("\nQtd de retornos por vértice preto null ou visitado: %llu\n", qtd_bound_null_black_visited);
	printf("\nQtd de retornos por grau de algum vizinho == 1: %llu\n", qtd_bound_grau_vizinho_1);
}

/*esvazia a pilha e outras variáveis para permitir o restart do GRASP*/
void reset_stack(){
	head_solucao_parcial = 0;
	pontuacao_parcial = 0;
	for(int i = 0; i < total_free_vertexes+1; i++){
		solucao_parcial[i] = 0;
	}
	for(int i = 0; i < m_*n_*4; i++){
		stack[i] = 0;
	}
	head_stack = -1;
	vertex_restantes= total_free_vertexes;

	for (int i = 0; i < m_; i++){
		for (int j = 0; j < n_; j++){
			matrix[i][j].visited = false;
			matrix[i][j].d = new_dice(i,j);
		}
	}

}

void init_data(){
	vertex** solucao_parcial_temp = (vertex**) malloc(sizeof(vertex*)*(total_free_vertexes+1));
	solucao_parcial = &solucao_parcial_temp[1];//Permitindo que o índice -1 guarde o vértice de origem

	head_solucao_parcial = 0;
	pontuacao_parcial = 0;

	melhor_solucao = (vertex**) malloc(sizeof(vertex*)*total_free_vertexes);
	pontuacao_melhor_solucao = 0;

	stack = (vertex**) malloc(sizeof(vertex*)*m_*n_*4);
	head_stack = -1;

	vertex_restantes = total_free_vertexes;

	//Parte da busca em profundidade
	vertex_visitados_profundidade = (vertex**) malloc(sizeof(vertex*)*total_free_vertexes);
	vertex_atingidos = 0;

	count_branches = 0;
	qtd_solucoes_validas = 0;
	qtd_bound_pontuacao_max = 0;
	qtd_bound_null_black_visited = 0;
	qtd_bound_grau_vizinho_1 = 0;

	//Parte do GRASP
	solucoes_iniciais = (vertex***) malloc(sizeof(vertex**)*populacao_solucao_inicial);
}

/** Configura o array de pontuacao maxima para N jogadas*/
void config_pontuacao_max(){
	int qtd_jogadas_alocar = total_free_vertexes+1;
	if (qtd_jogadas_alocar < 22)
		qtd_jogadas_alocar = 22;
	pontuacao_max_para_cada_numero_jogadas = malloc((sizeof(int)*qtd_jogadas_alocar));

	pontuacao_max_para_cada_numero_jogadas[0] = 0;
	pontuacao_max_para_cada_numero_jogadas[1] = 6;
	pontuacao_max_para_cada_numero_jogadas[2] = 11;
	pontuacao_max_para_cada_numero_jogadas[3] = 15;
	pontuacao_max_para_cada_numero_jogadas[4] = 21;
	pontuacao_max_para_cada_numero_jogadas[5] = 24;
	pontuacao_max_para_cada_numero_jogadas[6] = 29;
	pontuacao_max_para_cada_numero_jogadas[7] = 33;
	pontuacao_max_para_cada_numero_jogadas[8] = 39;
	pontuacao_max_para_cada_numero_jogadas[9] = 49;
	pontuacao_max_para_cada_numero_jogadas[10] = 47;
	pontuacao_max_para_cada_numero_jogadas[11] = 51;
	pontuacao_max_para_cada_numero_jogadas[12] = 56;
	pontuacao_max_para_cada_numero_jogadas[13] = 59;
	pontuacao_max_para_cada_numero_jogadas[14] = 65;
	pontuacao_max_para_cada_numero_jogadas[15] = 68;
	pontuacao_max_para_cada_numero_jogadas[16] = 74;
	pontuacao_max_para_cada_numero_jogadas[17] = 77;
	pontuacao_max_para_cada_numero_jogadas[18] = 83;
	pontuacao_max_para_cada_numero_jogadas[19] = 86;
	pontuacao_max_para_cada_numero_jogadas[20] = 91;
	pontuacao_max_para_cada_numero_jogadas[21] = 95;
	pontuacao_max_para_cada_numero_jogadas[22] = 100;

	if (total_free_vertexes >= 23){
		for (int vertex_restantes = 23; vertex_restantes <= total_free_vertexes; vertex_restantes++){
			int pontuacao_max = 0;

			if (vertex_restantes%3 == 0)//se é um multiplo exato (trata n == 0)
				pontuacao_max = (vertex_restantes/3 * 6) + (vertex_restantes/3 * 5) + (vertex_restantes/3 * 4);
			else if (vertex_restantes%3 == 1)
				pontuacao_max = (vertex_restantes/3 * 6) + (vertex_restantes/3 * 5) + (vertex_restantes/3 * 4) + 6;
			else if (vertex_restantes%3 == 2)
				pontuacao_max = (vertex_restantes/3 * 6) + (vertex_restantes/3 * 5) + (vertex_restantes/3 * 4) + 6 + 5;

			pontuacao_max_para_cada_numero_jogadas[vertex_restantes] = pontuacao_max;
		}
	}
}


void init_graph(FILE *fp, int dice_i_pos, int dice_j_pos){
	char x;//char lixo

	fscanf (fp, "%d%c", &m_, &x);
	fscanf (fp, "%d%c", &n_, &x);
	int vertex_value = 0;

	matrix = (vertex**) calloc(m_, sizeof(vertex*));
	for (int j = 0; j < m_; j++){
		matrix[j] = (vertex*) calloc(n_, sizeof(vertex));
	}

	for (int i = 0; i < m_; i++){
		for (int j = 0; j < n_; j++){
			fscanf (fp, "%d%c", &vertex_value, &x);
			matrix[i][j].i = i;
			matrix[i][j].j = j;
			matrix[i][j].black = vertex_value == 0;
			matrix[i][j].visited = false;
			matrix[i][j].d = new_dice(i,j);
			if (!matrix[i][j].black)
				total_free_vertexes++;
		}
	}
	fclose(fp);
	origin = &matrix[dice_i_pos][dice_j_pos];
}


