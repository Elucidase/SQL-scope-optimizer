SELECT  I.id
       ,SUM(3) AS agg
FROM I
CROSS JOIN A
WHERE (I.i2 > 0 OR I.i2 < -10)
AND I.id = A.a1
AND I.i2 > 10
AND I.id > A.a3
AND ((I.id = A.a1 AND A.a3 > A.a4) OR (I.id = A.a2 AND A.a3 < A.a4))
GROUP BY  I.id