#include <iostream>
#include <regex>
#include <vector>
#include <string>
#include <algorithm>
#include <utility>
#include <list>
#include <sstream>
#include <cstdlib>
#include "minisat/minisat/core/Solver.h"
#include "minisat/minisat/core/SolverTypes.h"
#include <pthread.h>
#include <time.h>


using namespace Minisat;
using namespace std;

//Stores info. of the min vertex cover, including size and covered vertices in a graph.
class VertexCoverInfo 
{
public:
    size_t VxCv;
    vector<int> minVertexCover;
    size_t minVertexCoverSize;

    VertexCoverInfo(size_t VxCv, const vector<int>& minVertexCover, size_t minVertexCoverSize)
        : VxCv(VxCv), minVertexCover(minVertexCover), minVertexCoverSize(minVertexCoverSize) {}
};

//Describes a graph and its constructor, which initializes the graph with the specified number of vertices and vertex cover information.
class Graph 
{
public:
    size_t vertices;
    vector<int> edgesInPlot;
    vector<vector<int>> graphOutput;
    VertexCoverInfo vertexCoverInfo;
    std::vector<bool> vertex_cover;

    Graph() : vertices(0), graphOutput(0), vertexCoverInfo(0, {}, 0) {}
    Graph(int vertices) : vertices(vertices), graphOutput(vertices), vertexCoverInfo(0, {}, vertices) {}

    void Gen_Adj_Matrix();
    void setVertexCover();
    void StoreEdges(const std::vector<int>& edges);
    vector<int> CheckVertexCover(size_t VxCv);
    void printOutput(Graph &street);
    void minVertCvForGraph();
    std::vector<bool> APPROX_VC_1(std::vector<std::pair<int, int>>& edgeList, Graph& street);

};

void Graph::setVertexCover(){
    if (vertices == 0) {
        return;  // No vertices, nothing to do
    }
    vertex_cover = std::vector<bool>(vertices, false);

}
// This method is in charge of creating the adjacency matrix (graphOutput) using the graph's provided edges.
void Graph::Gen_Adj_Matrix() 
{
    if (vertices == 0) {
        return;  // No vertices, nothing to do
    }

    graphOutput = vector<vector<int>>(vertices, vector<int>(vertices, 0));

    for (size_t i = 0; i < edgesInPlot.size(); i += 2) 
    {
        int vertex1 = edgesInPlot[i];
        int vertex2 = edgesInPlot[i + 1];

        graphOutput[vertex1][vertex2] = 1;
        graphOutput[vertex2][vertex1] = 1;
    }
}


//Based on the provided input, this method stores the graph's edges. 
//The new set of edges is then added to the edgesInPlot vector after any previous edge data has been cleared.
void Graph::StoreEdges(const std::vector<int>& edges) 
{
    edgesInPlot.clear();
    edgesInPlot.reserve(edges.size());
    for (std::vector<int>::const_iterator it = edges.begin(); it != edges.end(); ++it) 
    {
        edgesInPlot.push_back(*it);
    }
}

//This method is responsible for determining a vertex cover of the graph given a specified size VxCv
//Have taken multiple online references for this section of code
vector<int> Graph::CheckVertexCover(size_t VxCv) 
{
    Solver solver;
    vector<vector<Lit>> Vertices;

    Vertices.reserve(vertices);

    //Set up the vertices' initial values in a 2D vector so that the vertex cover can be calculated.
    for (size_t i = 0; i < vertices; i++) 
    {
        Vertices.push_back(vector<Lit>());
        Vertices.back().reserve(VxCv);
        for (size_t j = 0; j < VxCv; j++) 
        {
            Vertices.back().push_back(mkLit(solver.newVar()));
        }
    }

    //Cond. 1: To ensure each vertex is covered at least once in the vertex cover.
    for (size_t i = 0; i < VxCv; i++) 
    {
        vec<Lit> clauses;
        for (size_t j = 0; j < vertices; j++) 
        {
            clauses.push(Vertices[j][i]);
        }
        solver.addClause(clauses);
    }

    //Cond. 2: To ensure no more than one literal is true for each vertex in the vertex cover.
    for (size_t i = 0; i < vertices; i++) 
    {
        for (size_t j = 0; j < VxCv - 1; j++) 
        {
            for (size_t k = j + 1; k < VxCv; k++) 
            {
                solver.addClause(~Vertices[i][j], ~Vertices[i][k]);
            }
        }
    }

    //Cond. 3: To ensure that at least one vertex in the vertex cover is true for each position in the cover.
    for (size_t i = 0; i < VxCv; i++) 
    {
        for (size_t j = 0; j < vertices - 1; j++) 
        {
            for (size_t k = j + 1; k < vertices; k++) 
            {
                solver.addClause(~Vertices[j][i], ~Vertices[k][i]);
            }
        }
    }

    //Cond. 4: // To ensure that at least one vertex in the vertex cover is true for each edge in the graph.
    for (size_t i = 0; i < edgesInPlot.size(); i += 2) 
    {
        vec<Lit> clauses;

        size_t Vert_1 = edgesInPlot[i];
        size_t Vert_2 = edgesInPlot[i + 1];

        for (size_t k = 0; k < VxCv; k++) 
        {
            Lit clause_1 = Vertices[Vert_1][k];
            Lit clause_2 = Vertices[Vert_2][k];

            clauses.push(clause_1);
            clauses.push(clause_2);
        }

        solver.addClause(clauses);
    }

    // This part of the code checks the satisfiability of the MiniSat solver and retrieves the minimum vertex cover if a solution exists.
    auto res = solver.solve();
    vector<int> cover;

    if (res) {
        for (size_t j = 0; j < VxCv; j++) 
        {
            bool satisfied = false;
            for (size_t i = 0; i < vertices; i++) 
            {
                if (solver.modelValue(Vertices[i][j]) == l_True) 
                {
                    cover.push_back(i);
                    satisfied = true;
                    break;
                }
            }
            if (!satisfied) 
            {
                cover.push_back(-1);
            }
        }
        return cover;
    } else {
        return {-1};
    }
}

std::vector<bool> Graph::APPROX_VC_1(std::vector<std::pair<int, int>>& edgeList, Graph& street)
{

    int n = vertices;
    street.setVertexCover();
 
    while (!edgeList.empty())
    {
        std::map<int, int> degreeCount;
 
        for (const auto& edge : edgeList)
        {
            degreeCount[edge.first]++;
            degreeCount[edge.second]++;
        }
 
        int maxDegreeVertex = -1;
        int maxDegree = -1;
 
        for (const auto& entry : degreeCount)
        {
            if (!vertex_cover[entry.first] && entry.second > maxDegree)
            {
                maxDegree = entry.second;
                maxDegreeVertex = entry.first;
            }
        }
 
        if (maxDegreeVertex == -1)
        {
            break;
        }
 
        vertex_cover[maxDegreeVertex] = true;
 
        auto it = std::remove_if(edgeList.begin(), edgeList.end(),
            [maxDegreeVertex](const std::pair<int, int>& edge) {
                return edge.first == maxDegreeVertex || edge.second == maxDegreeVertex;
            });
 
        edgeList.erase(it, edgeList.end());
 
        for (const auto& edge : edgeList)
        {
            if (edge.first == maxDegreeVertex)
            {
                degreeCount[edge.second]--;
            }
            else if (edge.second == maxDegreeVertex)
            {
                degreeCount[edge.first]--;
            }
        }
    }
    return vertex_cover;
}
//This method iteratively checks vertex covers of increasing sizes to determine the graph's minimal vertex cover.
void Graph::minVertCvForGraph() 
{
    for (size_t i = 1; i < vertices && vertexCoverInfo.minVertexCoverSize == vertices; i++) 
    {
        vertexCoverInfo.minVertexCover = CheckVertexCover(i);
        if (vertexCoverInfo.minVertexCover[0] != -1 && vertexCoverInfo.minVertexCover.size() < vertexCoverInfo.minVertexCoverSize) 
        {
            vertexCoverInfo.minVertexCoverSize = vertexCoverInfo.minVertexCover.size();
        }
    }
}

// This function parses the input string representing graph edges and extracts vertex pairs using regular expressions.
// This section is the modified version of the code from Assignment 2
vector<pair<int, int>> extractEdges(const string &edgesStr) 
{
    vector<pair<int, int>> return_data;
    regex regex_pattern("<(\\d+),(\\d+)>|\\{(\\d+),(\\d+)\\}");
    smatch match;

    string edgesStrCopy = edgesStr;

    while (regex_search(edgesStrCopy, match, regex_pattern)) 
    {
        try 
        {
            int v1 = match[1].length() ? stoi(match[1].str()) : stoi(match[3].str());
            int v2 = match[2].length() ? stoi(match[2].str()) : stoi(match[4].str());

            return_data.push_back(make_pair(v1, v2));
        } 
        catch (const invalid_argument &e) 
        {
            std::cerr << "Error: Invalid argument in extractEdges" << e.what() << endl;
        } 
        catch (const out_of_range &e) 
        {
            std::cerr << "Error: Out of range in extractEdges" << e.what() << endl;
        }

        edgesStrCopy = match.suffix().str();
    }

    return return_data;
}

void Graph::printOutput(Graph &street){
    	cout << "CNF-SAT-VC: ";
        if (!street.vertexCoverInfo.minVertexCover.empty()) {
                sort(street.vertexCoverInfo.minVertexCover.begin(), street.vertexCoverInfo.minVertexCover.end());
                for (size_t i = 0; i < street.vertexCoverInfo.minVertexCover.size(); i++) 
                    {
                        std::cout << street.vertexCoverInfo.minVertexCover[i] << " ";
                    }
                    std::cout << std::endl;
                } else {
                    throw runtime_error("No valid vertex cover found.");
                }
        std::cout << "APPROX-VC-1: ";
        bool first = true;
        int n = vertices;
        for (int i = 1; i < n; i++)
        {
            if (vertex_cover[i])
            {
                if (!first)
                {
                    std::cout << ",";
                }
                std::cout << i;
                first = false;
            }
        }
        std::cout << std::endl;
}

void* threadSAT_VC(void* arg) {
    Graph& street = *reinterpret_cast<Graph*>(arg);
	//CNF_SAT_VC(std::ref(vertex_num), std::ref(vec_E));
	clock_t start, finish;
	double duration;

	start = clock();
    street.minVertCvForGraph();
	finish = clock();

	duration = (double)(finish - start) / CLOCKS_PER_SEC;
	//cout << "the duration time is: " << duration << endl;

}

void* threadApprox_VC_1(void* arg) {
    auto args = static_cast<std::tuple<Graph*, vector<pair<int, int>>>*>(arg);
    Graph& street = *std::get<0>(*args);
    vector<pair<int, int>> edgePairs = std::get<1>(*args);
	clock_t start, finish;
	double duration;
	start = clock();
    street.APPROX_VC_1(edgePairs, street);
	finish = clock();

	duration = (double)(finish - start) / CLOCKS_PER_SEC;
	//cout << "the duration time is: " << duration << endl;
    return nullptr;

}

// This method creates a graph, stores edges, and uses the included Minisat solver to determine the minimal vertex cover by parsing the input line and interpreting instructions ('V' for indicating the number of vertices and 'E' for adding edges).
int ParseInput(const string &line, Graph &street) 
{
    istringstream iss(line);
    char command;
    iss >> command;

    try 
    {
        if (command == 'V') 
        {
            int numVertices;
            if (iss >> numVertices) 
            {
                if (numVertices <= 0) 
                {
                    // Clear the graph-related information and continue reading inputs
                    street.edgesInPlot.clear();
                    street.vertexCoverInfo.minVertexCover.clear();
                    street = Graph();  // This constructor should create an empty graph
                    return 0;
                } 
                else 
                {
                    street = Graph(numVertices + 1);
                }
            } 
            else 
            {
                throw invalid_argument("Invalid number of vertices");
            }
        } 
        else if (command == 'E') 
        {
            string edgesStr;
            if (iss >> edgesStr) 
            {
                vector<pair<int, int>> edgePairs = extractEdges(edgesStr);
                for (const auto &edge : edgePairs) 
                {
                    street.edgesInPlot.push_back(edge.first);
                    street.edgesInPlot.push_back(edge.second);
                }

                street.Gen_Adj_Matrix();
                street.vertexCoverInfo.VxCv = street.vertices;
				pthread_t threadio, thread0, thread1, thread2;
                pthread_create(&thread0, nullptr, threadSAT_VC, &street);
                std::tuple<Graph*, std::vector<std::pair<int, int>>> args(&street, edgePairs);
                pthread_create(&thread1, nullptr, threadApprox_VC_1, &args);
                pthread_join(thread0, nullptr);
                pthread_join(thread1, nullptr);
                street.printOutput(street);

                return 0;
            } 
            else 
            {
                throw invalid_argument("Invalid edge format");
            }
        } 
        else 
        {
            throw invalid_argument("Unknown command");
        }
    } 
    catch (const std::exception &e) 
    {
        std::cerr << "Error: " << e.what() << std::endl;
    }
}

//This main function reads and processes input lines, invoking ParseInput and handling exceptions, until the end of input is reached.
int main() 
{
    Graph street(0);
    std::string line;

    while (std::getline(std::cin, line)) 
    {
        if (line.empty() || std::all_of(line.begin(), line.end(), ::isspace)) 
        {
            continue;
        }

        try 
        {
            ParseInput(line, street);
        } 
        catch (const std::exception &e) 
        {
            // Do nothing in case of an exception; just continue reading inputs
        }
    }

    if (!std::cin.eof()) 
    {
        std::cerr << "Error: Input terminated unexpectedly." << std::endl;
    }

    return 0;
}
