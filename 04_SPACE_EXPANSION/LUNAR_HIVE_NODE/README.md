# Lunar Hive Node — Infraestrutura de Dados Lunar

- topologia: malha redundante com cache local
- sincronização: uplink diário + fallback em atraso de 6 h
- armazenagem: blocos imutáveis referenciados por hash
- resiliência: checksum duplo e quorum de 3 nós para qualquer restauração
