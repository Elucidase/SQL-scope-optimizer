SELECT  I.id
       ,SUM(CASE WHEN (I.id = A.a1 AND A.a3 > A.a4) OR (I.id = A.a2 AND A.a3 < A.a4) THEN 3 ELSE 0 END) AS agg
FROM I
CROSS JOIN A
WHERE (I.i2 > 0 OR I.i2 < -10)
AND (I.id = A.a1 OR I.id = A.a2)
AND (CASE WHEN I.i2 > 10 THEN I.id > A.a3 ELSE I.id < A.a3 END)
GROUP BY  I.id