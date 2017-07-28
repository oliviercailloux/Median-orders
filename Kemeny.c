#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>

#define MaxItem 50
#define Tree 3000000	// Taille max de l'arbre

FILE *FichTour;

int     T[MaxItem][MaxItem], TT[MaxItem][MaxItem];
int		Perm[MaxItem], Part[MaxItem], Id[MaxItem], Sum[MaxItem], O[MaxItem];
int		Pred[Tree], Val[Tree], Num[Tree];
int		NbItem, Kmax;

/*
 
 Lit une table des préférences et construit le tournoi majoritaire correspondant
 
 Construit un ordre total qui donne une borne sup de la somme des poids des arcs retour
 
 Par décomposition du tournoi en plusieurs partitions, 
 construit un ordre par partition, indique son score et la liste de ses arcs retour.
 Soit BestSc le plus petit score obtenu.
 
 Par Branch & Bound construit d'un ordre à écart inférieur ou égal à BestSc
 Si le programme arrive à construire un ordre, cet ordre est médian.
 Sinon, soit il n'y en a pas, soit l'arborescence dévelopée à plus de Tree noeuds.
 
 */

void LecTour()
{	int		i,j,k;
    char    Nom[50], Fich[50]="Data/";
	
	/*  Lit un fichier tournoi :
	 Le nb. d'Items,
	 Pour chaque item
	 une etiquette d'au plus 49 car 
	 NbItem valeurs
	 */
	printf("Nom du fichier Tournoi ");
	gets(Nom); strcat(Fich,Nom); strcat(Fich,".tour");
    //	printf("%s\n",Fich);
	FichTour = fopen(Fich,"r"); assert(FichTour != NULL);
    
	fscanf(FichTour,"%d",&NbItem);
    if (NbItem>MaxItem) exit(0);
	printf("# of items %d\n\n",NbItem);
	
	for (i=0; i<NbItem;i++)
	{ 	fscanf(FichTour,"%s",Nom); printf("%d : %s\n",i+1,Nom);
		Id[i]=i+1;
		for (j=0; j<NbItem; j++)
			fscanf(FichTour,"%d",&T[i][j]);
		// for (j=0; j<NbItem; j++) printf("%2d ",T[i][j]); printf("\n");
	}	printf("\n\n");
  	fclose(FichTour);
	
    for (i=0; i<NbItem; i++) T[i][i]=0;
	for (i=1; i<NbItem; i++)
		for (j=0; j<i; j++) 
			if (T[i][j]>T[j][i]) { T[i][j]=T[i][j]-T[j][i]; T[j][i]=0; }
			else if (T[i][j]<T[j][i]) { T[j][i]=T[j][i]-T[i][j]; T[i][j]=0; }
	for (j=0; j<NbItem; j++) Sum[j]=0;
	for (j=0; j<NbItem; j++)
	 	for (i=0; i<NbItem; i++) Sum[j] += T[i][j];
	if (NbItem>50) return;
	
	printf("Tournoi majoritaire\n\n");
	printf("      ");
	for (i=0; i<NbItem; i++) printf("%3d ",i+1); printf("\n");
	printf("      ");
	for (i=0; i<NbItem; i++) printf(" -- "); printf("\n");
	for (i=0; i<NbItem; i++)
	{   printf("%3d : ",Id[i]);
        for (j=0; j<NbItem; j++) 
			printf("%3d ",T[i][j]);
        printf("\n");
	}
	printf("      ");
	for (i=0; i<NbItem; i++) printf("%3d ",Sum[i]); 
	printf("\n\n");
	
	return;
	
}

void OrdSum()
{	int	i, j,jj, k=0, Sc=0, min;
	
	// Ordre des moins dominés
	for (j=0; j<NbItem; j++) Sc += Sum[j];	// somme des valeurs du tournoi
	while (k<NbItem)
	{   min=2*Sc+1;
		for (j=0; j<NbItem; j++)
			if (Sum[j]<min) {  min=Sum[j]; jj=j; }
		for (j=0; j<NbItem; j++) Sum[j] -= T[jj][j];
		//printf("%d ",jj+1); 
        O[k]=jj;
		Sum[jj]=2*Sc+1;
		k++;
	}
	return;
}

int	Score()
{	int	i,ii, j,jj, k, Sc=0, flag=1, sm, sp;
	
	while(flag)
	{   flag=0;
		for (i=0; i<NbItem-1; i++)
			if (T[O[i+1]][O[i]]>0) 
			{ j=O[i]; O[i]=O[i+1]; O[i+1]=j; flag=1; }
	}   
    //	for (i=0; i<NbItem; i++) printf("%d ",O[i]+1); //printf("\n");

	for (i=2; i<NbItem; i++)
	{   ii=O[i]; sm=0; flag=0;
		for (j=i-1; j>-1; j--)
		{   jj=O[j]; 
			if (T[ii][jj]>0) { flag=1; break; }
			else sm += T[jj][ii];
		}	
		if (flag==0 || T[ii][jj]<=sm) continue;
		sp=T[ii][jj];
		while (j>0 && T[ii][O[j-1]]>0)  // si le précédent est aussi dominé par ii
		{   j--; jj=O[j];
			sp += T[ii][jj];			
		}
		for (k=j+1; k<i; k++) sm += T[jj][O[k]];
		if (T[jj][O[i-1]]) sp += T[jj][O[i-1]];	// transposition au bout
		if (sp>sm) 
		{   k=O[j]; O[j]=O[i]; O[i]=k; 
			if (T[O[i]][O[i-1]]) { k=O[i-1]; O[i-1]=O[i]; O[i]=k; }
		}
	}   
	
	printf("Arcs retour : ");
	Sc=0;
	for (i=0; i<NbItem-1; i++)
	{   ii=O[i];
		for (j=i+1; j<NbItem; j++) 
		{   jj=O[j]; 
			if (T[jj][ii]) printf("(%d,%d) %d | ",jj+1,ii+1,T[jj][ii]);
			Sc += T[jj][ii]; 
		}	
	}	printf("\n");
	return Sc;
}

void OrdComp(int NbClas)
{	int		i,ii, j,jj, k,kk=0, clas, card, Sc, sum, min;
	float	Rmin;
	
    for (clas=1; clas<=NbClas; clas++)
    {	printf("Classe %d : ",clas);
        card=0;
        for (i=0; i<NbItem; i++) 
            if (Part[i]==clas) { printf("%d ",i+1); Id[card]=i; card++; }
        for (i=0; i<card; i++)
         	for (ii=0; ii<card; ii++)
				TT[i][ii]=T[Id[i]][Id[ii]];
        // Ordre du sous-tournoi
        Sc=0;
        for (j=0; j<card; j++) Sum[j]=0;
        for (j=0; j<card; j++)
        {	for (i=0; i<card; i++) Sum[j] += TT[i][j];
            Sc += Sum[j];	// somme des valeurs du tournoi
        }
        k=0; sum=0;
        while (k<card)
        {   min=2*Sc+1;
            for (j=0; j<card; j++)
                if (Sum[j]<min) {  min=Sum[j]; jj=j; }
            Perm[k]=jj;
            sum += min;
            for (i=0; i<card; i++)
                Sum[i] -= TT[jj][i];
            Sum[jj]=2*Sc+1;
            k++;
        }   printf(" : poids = %d\n",sum);
        for (k=0; k<card; k++) O[kk+k]=Id[Perm[k]];
        kk += card;
    }	printf("\n");
	return;
}

void Vue(int Kmax)
{	int	k;
	
	printf("Pred : "); for (k=1; k<Kmax; k++) printf("%2d ",Pred[k]); printf("\n");
	printf("Num  : "); for (k=1; k<Kmax; k++) printf("%2d ",Num[k]); printf("\n");
	printf("Val  : "); for (k=1; k<Kmax; k++) printf("%2d ",Val[k]); printf("\n");
	
	return;
}

main() 
{	int		i,ii, j,jj, k,kk, NbClas, Sc, BestSc;
    int     ScMin, card, Der, NbCl=0, Wal=0, Poids;
    
	/*		Calcule pour un tournoi pondéré des solutions approchées et si possible 
	 un ordre médian en développant une arborescence de sections commençantes.
	 */
	LecTour();    
	OrdSum(); Sc=Score(); 
    BestSc=Sc; 
    printf("Ordre croissant des poids des arcs retour %d\n",Sc);
    for (i=0; i<NbItem; i++) printf("%2d ",O[i]+1); printf("\n\n");
	
	// Recherche un ordre par décomposition du tournoi
	
    NbClas=1; // Partition suivant l'ordre en classes équilibrées
	while (NbClas<=1+NbItem/6)
	{	NbClas++;
		for (i=0; i<NbItem; i++)
		{	Part[O[i]]=1+i*NbClas/NbItem; Perm[O[i]]=i+1;  }
		printf("Decomposition en %d classes\n",NbClas); 
		OrdComp(NbClas);
		Sc=Score();
		printf("Ordre compose a %d classes : %d\n",NbClas,Sc);
		for (i=0; i<NbItem; i++) printf("%2d ",O[i]+1); printf("\n");
		if (Sc<BestSc) BestSc=Sc; 
		printf("\n\n");
    }
	printf("Recherche d'un ordre a distance au plus %d\n\n",BestSc);
	
    // Initialisation de l'arbre
    for (j=0; j<NbItem; j++) Sum[j]=0;
    ScMin=NbItem;
    for (j=0; j<NbItem; j++)
     	for (i=0; i<NbItem; i++) Sum[j] += T[i][j];
	
    Kmax=1;	// indice dans l'arbre
    for (i=0; i<NbItem; i++)
        if (Sum[i]<=BestSc)
        {   Num[Kmax]=i+1; Val[Kmax]=Sum[i]; Pred[Kmax]=0; Kmax++;  }
	//    Vue(Kmax); printf("\n");
    
    // On prolonge la feuille de Val minimum
    NbCl=0; Wal=0;
    while (NbCl<NbItem-1)
    {	Sc=BestSc+1;
        //for (k=1; k<Kmax; k++)
        for (k=Kmax-1; k>0; k--)
            if (Val[k]<Sc) {  Sc=Val[k]; kk=k; if (Sc==Wal) break; }
        if (Sc>BestSc) 
		{   printf("Yen a pas !\n"); 
			printf("Taille de l'arbre %d\n",Kmax-1);
			return(0);
		} // arret 
        Der=Num[kk]-1; Wal=Val[kk];
        //printf("Feuille %d, Der = %d, Wal = %d, sortis : ", kk, Der+1, Wal);
        // On marque le chemin à la racine dans Id
        for (i=0; i<NbItem; i++) Id[i]=0;
        NbCl=0; k=kk;
        while (k)
        {	Id[Num[k]-1]=1; 
            //printf("%d ",Num[k]); 
            NbCl++; k=Pred[k];  
        }   //printf("Id = "); for (i=0; i<NbItem; i++) printf("%d ",Id[i]);
        //printf("suivi de : ");
        for (i=0; i<NbItem; i++)
        {   if (Id[i]==1 || T[i][Der]>0) continue;
            Poids=0; 
			for (k=0; k<NbItem; k++)
			{   if (Id[k]==1 || k==i) continue;
				Poids += T[k][i];
            }	//printf("%d,%d | ",i+1,Poids);
            if (Wal+Poids>BestSc) continue;
            Pred[Kmax]=kk; Num[Kmax]=i+1; Val[Kmax]=Wal+Poids;
            Kmax++; if (Kmax==Tree) { printf("Trop de sommets\n"); return(0); }
        }   //printf("\n");
        Val[kk]=BestSc+1;
        //Vue(Kmax); getchar();
    }	//printf("\n");
	
    printf("Ordre median a ecart %d\n",Wal); 
    k=kk;
    for (i=NbItem-2; i>=0; i--)
    {	O[i]=Num[k]-1; k=Pred[k];  }
    for (i=0; i<NbItem; i++) if (Id[i]==0) O[NbItem-1]=i;
    for (i=0; i<NbItem; i++) printf("%2d ",O[i]+1); printf("\n\n");
	
	printf("Arcs-retour : ");
	Sc=0;
	for (i=0; i<NbItem-1; i++)
	{   ii=O[i];
		for (j=i+1; j<NbItem; j++) 
		{   jj=O[j]; 
			if (T[jj][ii]) printf("(%d,%d) %d | ",jj+1,ii+1,T[jj][ii]);
			Sc += T[jj][ii]; 
		}	
	}	printf("Somme des poids %d\n\n",Sc);
	
    printf("Taille de l'arbre %d\n",Kmax-1);
	printf("C'est fini\n");
	
	
}
