# Carbon Synthesis Logic — dados em diamante

A conversão de osso em diamante é tratada como função de preservação de dados:

\[ D(p, T) = k \cdot \ln(p) \cdot T^{\alpha} \]

- **p**: pressão (GPa)
- **T**: temperatura (K)
- **k**: constante de coerência de dados
- **α**: fator de integridade (> 1 assegura cristalização completa)

Parâmetros operacionais mínimos:
- p ≥ 5 GPa
- T ≥ 1800 K
- tempo ≥ 8 h

Rótulo de controle: toda amostra recebe hash duplo (SHA-256) antes e depois da transmutação para verificar continuidade de dados.
